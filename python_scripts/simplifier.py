"""
Dafny Simplifier v10 - Automatic simplification of Dafny programs.

This tool simplifies Dafny programs by iteratively removing lines that are not
present in an original (stripped) version, while ensuring the program still
verifies correctly. It is useful for cleaning up LLM-generated Dafny code by
removing unnecessary assertions, lemma calls, and proof hints.

Algorithm Overview:
    1. Preprocess the file to identify:
       - Declaration boundaries (methods, lemmas, functions, predicates)
       - Removable candidates (lines added to the original)
       - Dependencies between declarations
    2. Iterate through candidates in reverse order, attempting removal
    3. For each candidate, verify the modified program using Dafny
    4. If verification succeeds, keep the removal; otherwise, restore
    5. Repeat until no more simplifications are possible

Key Features:
    - Incremental verification using --filter-symbol for faster checks
    - Smart dependency tracking to avoid unnecessary re-verification
    - Batch removal attempts to reduce verification calls (optional, depending on candidate correlation)
    - Caching of verification results to avoid duplicate checks
    - Support for negative tests (marked with //@invalid)
    - Handles multi-line blocks (if, while, forall, calc, etc.)
    - Configurable parallel processing of multiple files
    - Topological processing of declarations from clients to suppliers to minimize retries
    - Possibility to exhaust all removal attempts within a declaration before moving on

Usage:
    # Single file simplification:
    simplify_file("original.dfy", "modified.dfy", "output.dfy")

    # Batch processing of a folder (parallel):
    simplify_folder("stripped_folder", "modified_folder", "output_folder", max_workers=2)

Author: João Pascoal Faria (jpf@fe.up.pt)
License: MIT License

Copyright (c) 2026 João Pascoal Faria

"""

# ==============================================================================
# Imports
# ==============================================================================

from __future__ import annotations
import atexit
import os
import re
import subprocess
import tempfile
import time
from collections import defaultdict, deque
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from hashlib import sha1
from typing import Optional
import threading


# ==============================================================================
# Configuration Parameters
# ==============================================================================

# Path to the Dafny executable (full path, or just "dafny.exe" if in PATH)
dafny_executable = r"TODO"

# Verbosity level:
#   0 = silent (no output)
#   1 = normal (progress and results)
#   2 = verbose (detailed debugging information)
verbose = 1

# Enable profiling to track time spent in different operations and several statistics 
enable_profiling = False

# Verification timeout settings (in seconds)
verifier_timeout = 5      # Initial timeout per verification call
max_verifier_timeout = 30   # Maximum timeout (used for retries and full declarations)

# Handle negative tests: programs with //@invalid markers that should fail verification
handle_negative_tests = True

# Use --filter-symbol to verify only the affected method/lemma (faster for body changes)
use_filter_symbol = True

# Group consecutive statements for batch removal before trying individual removal
optimize_sequence = True

# Batch removal settings: try removing multiple adjacent candidates at once.
# Theoretical analysis: for batch size k and individual removal probability p,
# expected verification attempts = 1 + k*(1-p^k). For batching to beat k individual
# attempts, we need p > (1/k)^(1/k), which has minimum ~0.69 at k=e. 
# Below that, batching would hurt if candidates were independent. However, adjacent
# candidates (e.g., related assertions, variable+usage) often have correlated
# removability, making their joint probability closer to p than p^k. We exploit
# this by restricting batches to adjacent/overlapping candidates within the same
# declaration body, and limiting to the first round (when correlation is highest).
max_batch_size = 1   # Maximum number of candidates to batch together (1 = no batching)
max_batch_lines = 10  # Maximum total lines in a batch
max_batch_attempts = 1  # Number of batch attempts before falling back to individual

# Number of cores for Dafny verifier (None for default, or integer)
num_cores = 2

# Parallel processing settings
max_workers = 1 # Number of parallel file workers (set to 1 for sequential)

# Process declarations in topological order (leaves first) to avoid wasted
# verification attempts on code that will be removed when its dependencies are removed.
# When True, declarations with no dependents are fully simplified first,
# then their callers, etc. This can significantly reduce verification calls.
use_topological_order = True

# Process sections in declarations by reverse order: header, spec, body.
reverse_decl_sections = True

# When true, tries to exhaust all removal attempts within a declaration
# before moving to the next declaration.
exhaust_declaration_removals = True

# ==============================================================================
# Logging
# ==============================================================================

# Create a timestamped log file for this session (in current folder)
_log_timestamp = time.strftime("%Y%m%d-%H%M%S")
log_file_path = f"simplifier_log_{_log_timestamp}.txt"

# Thread-safe logging for main process (important with parallel workers)
_log_lock = threading.Lock()
_log_file = None


def _get_log_file():
    """Get or create the log file handle (lazy initialization)."""
    global _log_file
    if _log_file is None:
        _log_file = open(log_file_path, "w", encoding="utf-8")
        atexit.register(lambda: _log_file.close() if _log_file else None)
    return _log_file


def log(message: str, level: int = 1) -> None:
    """
    Print message to screen (if verbose >= level) and always write to log file.

    Args:
        message: The message to output.
        level: Minimum verbosity level required to print to screen.
    """
    if verbose >= level:
        print(message)
    with _log_lock:
        log_file = _get_log_file()
        log_file.write(message + "\n")
        log_file.flush()  # Ensure immediate write for parallel processes


def log_worker(message: str, level: int = 1, worker_id: str = None) -> None:
    """
    Log message from a worker process.

    Args:
        message: The message to output.
        level: Minimum verbosity level required to print to screen.
        worker_id: Optional worker identifier for prefixing messages.
    """
    if worker_id:
        message = f"[{worker_id}] {message}"
    log(message, level)


# ==============================================================================
# Profiling
# ==============================================================================

@dataclass
class ProfileStats:
    """Statistics for profiling verification performance."""
    total_verifications: int = 0
    successful_verifications: int = 0
    failed_verifications: int = 0
    syntax_error_verifications: int = 0
    negative_test_failures: int = 0
    timeout_verifications: int = 0
    other_failures : int = 0
    cached_verifications: int = 0

    total_verification_time: float = 0.0
    min_verification_time: float = float('inf')
    max_verification_time: float = 0.0

    # Other times
    preprocessing_time: float = 0.0

    def add_verification(self, duration: float, success: int, cached: bool):
        """Record a verification attempt."""
        if not cached:
            self.total_verifications += 1
            self.total_verification_time += duration
            self.min_verification_time = min(self.min_verification_time, duration)
            self.max_verification_time = max(self.max_verification_time, duration)
            if success == 1:
                self.successful_verifications += 1
            else:
                self.failed_verifications += 1
                if success == -1:
                    self.syntax_error_verifications += 1
                elif success == -2:
                    self.timeout_verifications += 1
                elif success == -3:
                    self.negative_test_failures += 1
                else:
                    self.other_failures += 1
        else:
            self.cached_verifications += 1


    def merge(self, other: 'ProfileStats'):
        """Merge stats from another ProfileStats instance."""
        self.total_verifications += other.total_verifications
        self.successful_verifications += other.successful_verifications
        self.failed_verifications += other.failed_verifications
        self.syntax_error_verifications += other.syntax_error_verifications
        self.negative_test_failures += other.negative_test_failures
        self.cached_verifications += other.cached_verifications
        self.timeout_verifications += other.timeout_verifications
        self.other_failures += other.other_failures
        self.total_verification_time += other.total_verification_time
        if other.min_verification_time < self.min_verification_time:
            self.min_verification_time = other.min_verification_time
        if other.max_verification_time > self.max_verification_time:
            self.max_verification_time = other.max_verification_time
        self.preprocessing_time += other.preprocessing_time

    def print_summary(self):
        """Print profiling summary."""
        log(f"\n{'='*60}")
        log(f"PROFILING SUMMARY")
        log(f"{'='*60}")

        log(f"\nVerification Calls:")
        log(f"  Total verifications: {self.total_verifications}")
        log(f"  Successful: {self.successful_verifications}")
        log(f"  Failed: {self.failed_verifications}")
        log(f"  Syntax Errors: {self.syntax_error_verifications}")
        log(f"  Negative Test Failures: {self.negative_test_failures}")
        log(f"  Timeouts: {self.timeout_verifications}")
        log(f"  Other failures: {self.other_failures}")

        log(f"  Cached (skipped): {self.cached_verifications}")

        if self.total_verifications > 0:
            avg_time = self.total_verification_time / self.total_verifications
            log(f"\nVerification Time:")
            log(f"  Total: {self.total_verification_time:.1f}s ({self.total_verification_time/60:.1f}m)")
            log(f"  Average: {avg_time:.2f}s")
            log(f"  Min: {self.min_verification_time:.2f}s")
            log(f"  Max: {self.max_verification_time:.2f}s")

        if self.preprocessing_time > 0:
            log(f"\nOther Times:")
            log(f"  Preprocessing: {self.preprocessing_time:.2f}s")

        log(f"{'='*60}\n")


# ==============================================================================
# Dafny Verification
# ==============================================================================

def verify_dafny_file(contents: str, 
                      lines: list[str], 
                      handle_negative_tests: bool = handle_negative_tests,
                      filter_symbol: str = None, 
                      timeout: int = verifier_timeout,
                      profile_stats: ProfileStats = None) -> tuple[int, float, float]:
    """
    Verifies a Dafny file using the Dafny verifier.

    Args:
        contents: The contents of the Dafny file
        lines: The lines of the Dafny file
        handle_negative_tests: Whether to run negative tests
        filter_symbol: Optional method/function name to filter verification (uses --filter-symbol)
        timeout: Verification timeout in seconds
        profile_stats: Optional ProfileStats instance to record metrics

    Returns:
        Tuple of (success_code, duration) where:
        - success_code: 1 if verification succeeds, 0 if verification fails, -1 if syntax errors,
                        -2 if timeout, -3 if negative test failure
        - duration: time spent in verification (seconds), including checking negative tests if applicable
        - initial_duration: time spent in initial verification (seconds), excluding negative tests
    """
    verify_start = time.time()

    # Create a per-call temporary file (process-safe)
    temp_fd, temp_dafny_path = tempfile.mkstemp(suffix='.dfy', text=True)
    try:
        # Write to temporary file
        with os.fdopen(temp_fd, 'w', encoding='utf-8') as file:
            file.write(contents)

        # Build command
        cmd = [
            dafny_executable,
            "verify",
            temp_dafny_path,
            f"--verification-time-limit:{timeout}",
            "--allow-warnings:true"
        ]

        if num_cores is not None:
            cmd.append(f"--cores:{num_cores}")

        # filter by position seems not to work properly, so we filter by symbol only
        if filter_symbol:
            cmd.append(f"--filter-symbol={filter_symbol}.")
            # '.' added to avoid prefix matches

        # Run the verifier with timeout enforcement
        # Add buffer to timeout to allow Dafny to cleanup gracefully
        process_timeout = timeout + 5

        try:
            result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=process_timeout,
                check=False
            )
            stdout = result.stdout
        except subprocess.TimeoutExpired:
            # Process exceeded timeout - treat as verification failure
            initial_duration = time.time() - verify_start
            log(f"  Verification timed out after {process_timeout}s", level=2)
            return -2, initial_duration, initial_duration  # verification failed due to timeout
       
        initial_duration = time.time() - verify_start

        # Remove errors regarding counter-examples, to avoid confusion with normal errors
        cleaned = "\n".join(
            line for line in stdout.decode('utf-8').splitlines()
            if not line.startswith("Prover error")
        )        

        # Check for errors in output
        if "resolution/type errors" in cleaned or "parse errors" in cleaned:
            return -1, initial_duration, initial_duration  # syntax errors
        if not cleaned.endswith(' 0 errors'):
            if initial_duration >= timeout:
                return -2, initial_duration, initial_duration  # verification failed due to timeout
            else:
                return 0, initial_duration, initial_duration  # verification failed

        # Run negative tests (one at a time) if required
        if handle_negative_tests:
            for index in range(len(lines)):
                line = lines[index]
                if not line.strip().startswith("//@invalid"):
                    continue
                # Erase this string in this line
                old_line = line
                lines[index] = line.replace("//@invalid", "")
                new_content = "\n".join(lines)
                # Call the verifier again on the new file
                success, _, _ = verify_dafny_file(new_content, lines, False, filter_symbol, verifier_timeout, profile_stats)
                # restore the old line and continue
                lines[index] = old_line
                # If passes, return failure
                if success == 1:
                    total_duration = time.time() - verify_start
                    return -3, initial_duration, total_duration  # failure in negative tests

        total_duration = time.time() - verify_start
        return 1, initial_duration, total_duration  # success

    finally:
        # Clean up temporary file
        try:
            os.unlink(temp_dafny_path)
        except Exception:
            pass  # Ignore cleanup errors


# ==============================================================================
# Data Structures for File Analysis
# ==============================================================================


@dataclass
class DeclarationInfo:
    """
    Information about a Dafny declaration (method, lemma, function, or predicate).

    Attributes:
        name: The identifier name of the declaration.
        kind: "M" for method/lemma, "F" for function/predicate.
        header_start: Line number where the declaration starts (0-indexed).
        body_start: Line number where the body begins (after requires/ensures).
        end_line: Line number where the declaration ends.
        timestamp_spec: Timestamp of last change that created opportunities for specification minimization (requires/ensures).
        timestamp_body: Timestamp of last change that created opportunities for body minimization.
        ref_count: Number of references to this declaration from other declarations.
    """
    name: str
    kind: str
    header_start: int
    body_start: int
    end_line: int
    timestamp_spec: int = 0
    timestamp_body: int = 0
    ref_count: int = 0
    scc_id: int = -1  # strongly connected component id for topological ordering


@dataclass
class RemovalCandidate:
    """
    A candidate for removal during simplification (single line or block).

    Attributes:
        id: Unique identifier for this candidate.
        start_line: Starting line number (0-indexed).
        end_line: Ending line number (same as start_line for single lines).
        enclosing_decl: The declaration containing this candidate, if any.
        enclosing_location: Location within declaration:
            "H" = header, "S" = specification, "B" = body, None = global.
        replace_with: Replacement text when removing (e.g., "}" for "} else"),
            or None for complete removal.
        timestamp_last_attempt: When this candidate was last attempted.
        num_attempts: Total removal attempts for this candidate.
        max_attempts: Maximum allowed attempts (-1 = unlimited).
        num_batch_attempts: Number of times included in batch removal attempts.
    """
    id: int
    start_line: int
    end_line: int
    enclosing_decl: Optional[DeclarationInfo]
    enclosing_location: Optional[str]
    replace_with: Optional[str]
    timestamp_last_attempt: int = 0
    num_attempts: int = 0
    max_attempts: int = -1
    num_batch_attempts: int = 0
    outgoing_refs: int = 0  # number of references from this candidate to other declarations


@dataclass
class FileStructure:
    """
    Preprocessed structure of a Dafny file.

    This structure is computed once during preprocessing and updated incrementally
    as lines are removed. It contains all information needed for efficient
    simplification without re-parsing the file.

    Attributes:
        lines: Current lines of the file.
        candidates: List of removal candidates.
        declarations: Map from declaration name to DeclarationInfo.
        contains_negative_tests: True if file has //@invalid markers.
        decls_with_negative_tests: Set of declaration names containing //@invalid markers.
            Used to determine when negative tests need to be re-verified.
        dependencies: Map (A, B) -> count where A calls/references B.
            Count > 0 means direct dependency, count = 0 means indirect (transitive).
        deps_spec: Map (A, B) -> count where A's spec references B.
            Used for fine-grained retry decisions.
        deps_body: Map (A, B) -> count where A's body references B.
            Used for fine-grained retry decisions.
        removable_decls: Set of declaration names that can be fully removed
            (no other declarations depend on them).
    """
    lines: list[str]
    candidates: list[RemovalCandidate]
    declarations: dict[str, DeclarationInfo]
    contains_negative_tests: bool
    decls_with_negative_tests: set[str]
    dependencies: dict[tuple[str, str], int]
    deps_spec: dict[tuple[str, str], int]
    deps_body: dict[tuple[str, str], int]
    removable_decls: set[str]



# ==============================================================================
# Matching Utilities (Modified to Original Lines)
# ==============================================================================

# Regex to normalize lines: remove comments, attributes, and whitespace
_NORMALIZE_PATTERN = re.compile(r'//.*$|\{:[^}]*\}|\s+')


def normalize_line(line: str) -> str:
    """
    Normalize a line for comparison by removing comments, attributes, and whitespace.

    This allows comparing lines that differ only in formatting or annotations.

    Args:
        line: The source line to normalize.

    Returns:
        Normalized string with comments, attributes, and whitespace removed.
    """
    return _NORMALIZE_PATTERN.sub('', line)



def compute_subsequence_matching(
    modified_normalized: list[str],
    original_normalized: list[str],
) -> list[int]:
    """
    Fast O(m+n) subsequence matching between modified and original lines.

    Maps each line in the modified file to its corresponding line in the original
    file, if one exists. Empty normalized lines are skipped.

    This function assumes the original is a subsequence of the modified file
    (i.e., all original lines appear in the same order in the modified file).
    If this assumption fails, it falls back to LCS-based matching.

    Args:
        modified_normalized: Normalized lines from the modified file.
        original_normalized: Normalized lines from the original file.

    Returns:
        List where result[i] = j means modified line i matches original line j,
        or -1 if modified line i has no match (was added).
    """
    mod2orig = [-1] * len(modified_normalized)

    i = 0  # index of modified file
    j = 0  # index of original file

    while i < len(modified_normalized) and j < len(original_normalized):
        if original_normalized[j] == "":
            j += 1
            continue

        if modified_normalized[i] == "":
            i += 1
            continue

        if modified_normalized[i] == original_normalized[j]:
            mod2orig[i] = j
            j += 1

        i += 1

    # check if remaining lines are empty
    while j < len(original_normalized):
        if original_normalized[j] != "":
            # fallback to LCS-based matching
            return compute_lcs_matching(modified_normalized, original_normalized)
        j += 1

    return mod2orig

def compute_lcs_matching(modified_normalized: list[str], original_normalized: list[str]) -> list[int]:
    """
    Compute line matching using Longest Common Subsequence (LCS) algorithm.

    This is a fallback for when the fast subsequence matching fails.
    Uses O(n) space optimization instead of O(m*n).

    Args:
        modified_normalized: Normalized lines from the modified file.
        original_normalized: Normalized lines from the original file.

    Returns:
        List where result[i] = j means modified line i matches original line j,
        or -1 if no match exists.
    """
    m, n = len(modified_normalized), len(original_normalized)
    if n == 0:
        return [-1] * m

    # Use only 2 rows instead of m+1 rows
    prev = [0] * (n + 1)
    curr = [0] * (n + 1)

    # Store backtracking info separately (only when needed)
    backtrack = {}  # (i, j) -> direction

    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if modified_normalized[i - 1] == original_normalized[j - 1]:
                curr[j] = prev[j - 1] + 1
                backtrack[(i, j)] = 'match'
            else:
                if prev[j] >= curr[j - 1]:
                    curr[j] = prev[j]
                    backtrack[(i, j)] = 'up'
                else:
                    curr[j] = curr[j - 1]
                    backtrack[(i, j)] = 'left'
        prev, curr = curr, prev
        curr = [0] * (n + 1)

    # Reconstruct matching using backtrack dict
    result = [-1] * m
    i, j = m, n
    while i > 0 and j > 0:
        direction = backtrack.get((i, j))
        if direction == 'match':
            result[i - 1] = j - 1
            i -= 1
            j -= 1
        elif direction == 'up':
            i -= 1
        else:
            j -= 1

    return result


# ==============================================================================
# Dependency Analysis
# ==============================================================================


def transitive_closure_dependencies_typed(
    deps_spec: dict[tuple[str, str], int],
    deps_body: dict[tuple[str, str], int],
    decl_kind: dict[str, str],
) -> dict[tuple[str, str], int]:
    """
    Compute transitive closure of declaration dependencies.

    This function merges specification and body dependencies, then computes
    the transitive closure to find all indirect dependencies. The traversal
    rules differ by declaration kind:

    - Methods/lemmas ("M"): Only spec dependencies propagate (body is opaque)
    - Functions/predicates ("F"): Both spec and body dependencies propagate

    Args:
        deps_spec: Direct dependencies from specifications {(A, B): count}.
        deps_body: Direct dependencies from bodies {(A, B): count}.
        decl_kind: Map from declaration name to kind ("M" or "F").

    Returns:
        Combined dependency dict where:
        - Direct edges have positive counts (spec + body summed)
        - Indirect (transitive-only) edges have count = 0
    """
    # Initiate result with direct edges (counts are real)
    # and build adjacency lists for traversal
    result = defaultdict(int)
    succ_spec = defaultdict(set)
    succ_all  = defaultdict(set)
    nodes = decl_kind.keys()

    for (a, b), cnt in deps_spec.items():
        result[(a, b)] += cnt
        succ_spec[a].add(b)
        succ_all[a].add(b)

    for (a, b), cnt in deps_body.items():
        result[(a, b)] += cnt
        succ_all[a].add(b)

    # Add transitive reachability edges (from spec to decl (body in fun/pred)) with count 0
    for start in nodes:
        seen = set([start])
        q = deque([start])
        while q:
            cur = q.popleft()
            succ = succ_spec.get(cur, ()) if decl_kind[cur] == "M" else succ_all.get(cur, ())
            for nxt in succ:
                if nxt not in seen:
                    seen.add(nxt)
                    q.append(nxt)
                    if nxt != start and (start, nxt) not in result:
                        result[(start, nxt)] = 0  # indirect edge
                        log(f"  Added indirect dependency edge: {start} -> {nxt}", level=2)


    return result


# ==============================================================================
#  Parsing Utilities
# ==============================================================================

# Similar, restricted to methods and lemmas only
METHOD_LIKE_STARTERS = [
    "method", "lemma", "ghost method", "ghost lemma"
]

# And to functions and predicates only
FUNCTION_LIKE_STARTERS = [
    "function", "predicate", "ghost function", "ghost predicate"
]

# Keywords that start a declaration, combining the previous two
DECLARATION_STARTERS = METHOD_LIKE_STARTERS + FUNCTION_LIKE_STARTERS

# Keywords for specification clauses
CLAUSE_KEYWORDS = ["requires", "ensures", "modifies", "decreases", "reads",
                   "invariant", "fresh"]

# Keywords/patterns that start a multi-line block
BLOCK_INITIATORS = [
    "calc ", "forall ", "if ", "else", "calc{", "if(",
    "for ", "while ", "while(", "by ", "} else"
]

# Regex to skip braces inside multiset{}, set{}, attributes {:...}, and string literals
_BRACE_SKIP_PATTERN = re.compile(
    r'multiset\{[^}]*\}|'   # multiset literals
    r'\{:[^}]+\}|'          # attributes like {:fuel 3}
    r'set\{[^}]*\}|'        # set literals
    r'"(?:[^"\\]|\\.)*"|'   # double-quoted strings
    r"'(?:[^'\\]|\\.)*'"    # single-quoted strings/chars
)


def count_braces_in_line(line: str) -> tuple[int, int]:
    """
    Count opening and closing braces in a line, ignoring those in literals/attributes.

    Returns:
        Tuple of (open_brace_count, close_brace_count).
    """
    cleaned = _BRACE_SKIP_PATTERN.sub('', line)
    return cleaned.count('{'), cleaned.count('}')


def get_decl_kind(decl_header_line: str) -> str:
    """
    Classify a declaration as method-like or function-like.

    Args:
        decl_header_line: The first line of the declaration.

    Returns:
        "M" for method/lemma (opaque body), "F" for function/predicate
        (transparent body), or "?" for unknown.
    """
    s = decl_header_line.strip()
    # similar but using the above constants for starters

    if s.startswith(tuple(METHOD_LIKE_STARTERS)):
        return "M"
    if s.startswith(tuple(FUNCTION_LIKE_STARTERS)):
        return "F"
    return "?"


def _find_next_line_non_empty(lines: list[str], start_index: int) -> int:
    """
    Find the next non-empty line after start_index.

    Args:
        lines: All lines of the file.
        start_index: Line to start searching from.

    Returns:
        Line index of the next non-empty line, or len(lines) if none found.
    """
    for i in range(start_index + 1, len(lines)):
        if lines[i].strip():
            return i
    return len(lines)


def _find_block_end(lines: list[str], start_index: int) -> tuple[int, Optional[str]]:
    """
    Find the end of a brace-delimited block starting at start_index.

    Handles if/else chains by continuing past closing braces followed by "else".

    Args:
        lines: All lines of the file.
        start_index: Line where the block starts.

    Returns:
        Tuple of (end_line_index, replacement_text). The replacement_text is
        non-None for special cases like "} else" (replace with "}") or
        "by {" blocks (replace with ";").
    """
    line = lines[start_index].strip()

    # Determine initial brace count adjustment
    if line.startswith("}"):
        initial_offset = -1
    else:
        initial_offset = 0

    open_count = 0
    close_count = initial_offset

    for i in range(start_index, len(lines)):
        line_to_check = lines[i]
        stripped = line_to_check.strip()

        # Abort if we hit a new declaration
        if i > start_index and any(stripped.startswith(token + " ") or stripped.startswith(token + "(")
                                   for token in DECLARATION_STARTERS):
            break

        o, c = count_braces_in_line(line_to_check)
        open_count += o
        close_count += c

        if open_count == close_count and open_count > 0:
            # Check for else continuation
            if (re.search(r'\belse\b', line_to_check) or 
                (i < len(lines) - 1 and re.search(r'\belse\b', lines[i + 1]))):
                continue

            # Determine replacement
            replace_with = None
            leading = re.match(r'^\s*', lines[start_index]).group(0)

            if line.startswith("} else"):
                replace_with = leading + "}"
            elif line.startswith("by "):
                replace_with = leading + ";"

            return i, replace_with

    return start_index, None


def _find_statement_end(lines: list[str], start_index: int) -> int:
    """
    Find the end of a multi-line statement terminated by semicolon.

    Args:
        lines: All lines of the file.
        start_index: Line where the statement starts.

    Returns:
        Line index where the statement ends (line containing ';').
    """
    for i in range(start_index + 1, len(lines)):
        stripped = lines[i].strip()
        # ignore text after '//' when checking for ';'
        code_part = stripped.split("//")[0].rstrip()
        if code_part.endswith(";"):
            return i
    return start_index


def _find_clause_end(lines: list[str], start_index: int) -> int:
    """
    Find the end of a multi-line specification clause.

    Specification clauses (requires, ensures, invariant, etc.) can span
    multiple lines. A clause ends when the next line:
    - Is empty or whitespace only
    - Starts with an opening brace '{'
    - Starts with another clause keyword
    - Starts with a declaration keyword

    Args:
        lines: All lines of the file.
        start_index: Line where the clause starts.

    Returns:
        Line index where the clause ends.
    """
    for i in range(start_index + 1, len(lines)):
        stripped = lines[i].strip()

        # Empty line ends the clause
        if not stripped:
            return i - 1

        # Opening brace ends the clause
        if stripped.startswith("{"):
            return i - 1

        # Another clause keyword ends the current clause
        if any(stripped.startswith(kw) for kw in CLAUSE_KEYWORDS):
            return i - 1

        # A declaration starts (we've gone too far)
        if any(stripped.startswith(decl + " ") or stripped.startswith(decl + "(")
               for decl in DECLARATION_STARTERS):
            return i - 1

    return start_index


# ==============================================================================
# File Preprocessing
# ==============================================================================


def preprocess_file(lines: list[str], original_lines: list[str] = None) -> FileStructure:
    """
    Preprocess a Dafny file to extract structural information.

    This is the main analysis function that runs once at the start. It:
    1. Parses declaration boundaries (methods, lemmas, functions, predicates)
    2. Computes line matching between modified and original files
    3. Identifies removable candidates (lines not in original)
    4. Determines block boundaries for multi-line constructs
    5. Builds the dependency graph between declarations

    Args:
        lines: Lines of the modified file to simplify.
        original_lines: Lines of the original file for comparison.
            Lines matching the original will not be considered for removal.

    Returns:
        FileStructure containing all preprocessed information needed for
        efficient incremental simplification.
    """
    # Normalize original lines for comparison
    original_normalized = []
    if original_lines:
        original_normalized = [normalize_line(line) for line in original_lines]

    # First pass: compute brace depths and find declarations
    current_depth = 0
    declarations = {}
    dependencies = {}

    # Track current declaration being parsed
    current_decl_name = None
    current_decl_header_start = -1
    current_decl_body_start = -1  # Line where the body starts (first opening brace)
    current_decl_depth = 0
    current_decl_kind = None

    for i, line in enumerate(lines):
        open_count, close_count = count_braces_in_line(line)
        stripped = line.strip()

        # Check for declaration start
        for starter in DECLARATION_STARTERS:
            if stripped.startswith(starter + " ") or stripped.startswith(starter + "("):
                # Extract name - handle optional attributes like {:fuel 3} between keyword and name
                # Pattern: ghost? keyword (attributes)* name
                match = re.match(rf'^(?:ghost\s+)?{starter}\s+(?:\{{:[^}}]+\}}\s*)*([A-Za-z_][A-Za-z0-9_]*)', stripped)
                if match and current_decl_name is None:
                    current_decl_name = match.group(1)
                    current_decl_header_start = i
                    current_decl_body_start = -1  # Will be set when we see the first {
                    current_decl_depth = current_depth
                    current_decl_kind = get_decl_kind(stripped)

        # Track body start (first opening brace after declaration header)
        if current_decl_name is not None and current_decl_body_start == -1 and open_count > 0:
            # exclude lines with ensures, requires, modifies, reads, decreases
            if not any(stripped.startswith(clause) for clause in CLAUSE_KEYWORDS):
                current_decl_body_start = i

        current_depth += open_count - close_count

        # Check for declaration end
        # A declaration ends when:
        # 1. We're back to the original brace depth
        # 2. We've seen the body start (opening brace)
        # 3. We're past the header line (to handle single-line and multi-line declarations)
        if current_decl_name is not None:
            if (current_depth == current_decl_depth and
                current_decl_body_start >= 0 and
                i >= current_decl_body_start):
                #exclude lines with ensures, requires, modifies, reads, decreases
                if not any(stripped.startswith(clause) for clause in CLAUSE_KEYWORDS):
                    # Declaration body ended - store header_start, body_start, end
                    body_start = current_decl_body_start
                    new_decl = DeclarationInfo(
                        name=current_decl_name,
                        kind=current_decl_kind,
                        header_start=current_decl_header_start,
                        body_start=body_start,
                        end_line=i,
                        timestamp_body=0,
                        timestamp_spec=0,
                        ref_count=0,
                        scc_id=-1
                    )
                    declarations[current_decl_name] = new_decl
                    current_decl_name = None
                    current_decl_header_start = -1
                    current_decl_body_start = -1
                    current_decl_kind = None


    # Compute LCS-based matching between modified and original lines
    modified_normalized = [normalize_line(line) for line in lines]
    lcs_matching = compute_subsequence_matching(modified_normalized, original_normalized)

    # Second pass: build removal candidates with all preprocessed data
    candidates = []
    # queue of candidates corresponding to start of blocks to be inserted later at end of block
    candidate_queue = deque()

    for i, line in enumerate(lines):
        stripped = line.strip()
        normalized = modified_normalized[i]

        if normalized == "":
            continue

        # Get the LCS-based match for this line
        original_match = lcs_matching[i]

        # Check if is removable (still needed after other checks below)
        is_removable = not (normalized == "{" or
                           normalized == "}" or normalized == "{}") and original_match == -1  # Only removable if not matching original

        # Find enclosing declaration (method/lemma/function/predicate) and location within it
        enclosing_decl = None
        enclosing_location = None
        for decl in declarations.values():
            if decl.header_start <= i <= decl.end_line:
                enclosing_decl = decl
                if i == decl.header_start:
                    enclosing_location = "H"  # Header line
                elif decl.header_start <= i < decl.body_start:
                    enclosing_location = "S"  # Spec (requires/ensures/etc.)
                else:
                    enclosing_location = "B"  # Body
                break

        # Determine block end and replace_with
        block_end = -1
        replace_with = None

        # Track if we need to add a second RemovalCandidate for "assert...by" statements
        by_replace_with = None
        is_block_start = False
        code_part = stripped.split("//")[0].rstrip()

        # Check if this is a declaration start
        if enclosing_location == "H":
            block_end = enclosing_decl.end_line
        # Check if this starts a block
        elif any(code_part.startswith(token) for token in BLOCK_INITIATORS):
            block_end, replace_with = _find_block_end(lines, i)
            is_block_start = True
        elif code_part.startswith("assert ") and " by {" in code_part:
            # Assert with inline "by {" block - create TWO options:
            # 1. Remove entire statement (this RemovalCandidate)
            # 2. Replace just the "by {...}" part with ";" (second RemovalCandidate below)
            block_end, _ = _find_block_end(lines, i)
            if block_end > i:
                is_block_start = True
            # Prepare second option: replace "by {...}" with ";"
            by_replace_with = line[:line.find(" by {")] + ";"
        elif (code_part.startswith("assert ") or code_part.startswith("==")) and not code_part.endswith(";"):
            if code_part.startswith("assert ")  and i + 1 < len(lines) and lines[i + 1].strip().startswith("by "):
                block_end, _ = _find_block_end(lines, i)
                if block_end > i:
                    is_block_start = True
            else:
                block_end = _find_statement_end(lines, i)
        elif any(code_part.startswith(clause) for clause in CLAUSE_KEYWORDS):
            # Multiline clause - find the end of the clause
            block_end = _find_clause_end(lines, i)
            # don't remove ensures after forall statements (only together with the whole forall)
            if code_part.startswith("ensures") and i > 0 and lines[i - 1].strip().startswith("forall "):
                is_removable = False
        elif stripped.startswith("}") and not stripped.startswith("} else"):
            # Don't remove closing braces alone
            is_removable = False
        # non removable first line after "calc {" pattern in previous line
        elif i > 0 and lines[i - 1].strip().startswith("calc {"):
            is_removable = False
        else:
            # Single line
            block_end = i

        # Not removable inside body of functions/predicates
        if enclosing_decl is not None and enclosing_decl.kind == "F" and enclosing_location == "B":
            is_removable = False

        if is_removable:
            # For "assert...by" statements, add a second RemovalCandidate for "replace by with ;" option
            if by_replace_with is not None:
                candidates.append(RemovalCandidate(
                    id=0,
                    start_line=i,
                    enclosing_decl=enclosing_decl,
                    enclosing_location=enclosing_location,
                    end_line=block_end,
                    replace_with=by_replace_with  # Replace with "assert ...;"
                ))


                # Add primary RemovalCandidate (full removal option)
            new_candidate = RemovalCandidate(
                id=0, # to be determined later
                start_line=i,
                enclosing_decl=enclosing_decl,
                enclosing_location=enclosing_location,
                end_line=block_end,
                replace_with=replace_with
            )

            if is_block_start and block_end > i:
                candidate_queue.append(new_candidate)
            else:
                candidates.append(new_candidate)

        # pop from queue blocks that end here (start from the ones added later)
        while candidate_queue and candidate_queue[-1].end_line == i:
            queued_candidate = candidate_queue.pop()
            candidates.append(queued_candidate)
            log(f"Added queued removable block from line {queued_candidate.start_line+1} to line {i+1}", level=2)

    # check sequences of removable isolated lines and add at the end a new candidate
    # for the entire sequence (at least for first attempt)
    if optimize_sequence:
        i = 0
        while i < len(candidates):
            info = candidates[i]
            stripped = lines[info.start_line].strip()
            if (info.enclosing_location != "B" or
                info.replace_with is not None or
                stripped.startswith("invariant") or
                stripped.startswith("decreases")):
                i += 1
                continue
            start = info.start_line
            end = info.end_line
            j = i
            while j + 1 < len(candidates):
                next_info = candidates[j+1]
                if (next_info.enclosing_location == "B" and
                    next_info.replace_with is None and
                    next_info.start_line == _find_next_line_non_empty(lines, end)):
                    end = next_info.end_line
                    j += 1
                else:
                    break
            if i == j:
                i += 1
                continue
            # add new RemovalCandidate for the entire sequence
            new_candidate = RemovalCandidate(
                id=0,
                start_line=start,
                enclosing_decl=info.enclosing_decl,
                enclosing_location=info.enclosing_location,
                end_line=end,
                replace_with=None,
                max_attempts=1  # only one attempt for the entire sequence
            )
            # insert after j
            candidates.insert(j + 1, new_candidate)
            # advance i
            i = j + 2

    # Check for negative tests and find which declarations contain them
    contains_negative_tests = any("@invalid" in line for line in lines)
    decls_with_negative_tests = set()
    if contains_negative_tests:
        for decl in declarations.values():
            # Check if any line in this declaration contains @invalid
            for i in range(decl.header_start, decl.end_line + 1):
                if "@invalid" in lines[i]:
                    decls_with_negative_tests.add(decl.name)
                    break

    deps_spec = {}
    deps_body = {}
    decl_kind = {}

    # Pre-compile regex patterns for each declaration name (v9 optimization)
    decl_patterns = {name: re.compile(rf'\b{re.escape(name)}\s*\(')
                     for name in declarations.keys()}

    # count references between declarations using pre-compiled patterns
    for decl in declarations.values():
        decl_kind[decl.name] = decl.kind

        spec_text = "\n".join(lines[decl.header_start:decl.body_start]) if decl.body_start > decl.header_start else lines[decl.header_start]
        body_text = "\n".join(lines[decl.body_start:decl.end_line+1]) if decl.body_start >= 0 else ""


        for other_decl in declarations.keys():
            if other_decl == decl.name:
                continue

            # Use pre-compiled pattern (v9 optimization)
            pattern = decl_patterns[other_decl]

            c_spec = len(pattern.findall(spec_text))
            if c_spec > 0:
                deps_spec[(decl.name, other_decl)] = deps_spec.get((decl.name, other_decl), 0) + c_spec

            c_body = len(pattern.findall(body_text))
            if c_body > 0:
                deps_body[(decl.name, other_decl)] = deps_body.get((decl.name, other_decl), 0) + c_body

            declarations[other_decl].ref_count += c_spec + c_body

    # compute closure (indirect edges will have 0 counters)
    dependencies = transitive_closure_dependencies_typed(deps_spec, deps_body, decl_kind)

    # Initially all removable candidates need rechecking
    removable_decls = set()
    for info in candidates:
        enclosing_decl =  info.enclosing_decl
        if enclosing_decl is not None:
            if info.enclosing_location == "B":
                enclosing_decl.timestamp_body = 1
            elif info.enclosing_location == "S":
                enclosing_decl.timestamp_spec = 1
            elif info.enclosing_location == "H":
                enclosing_decl.timestamp_spec = 1
                enclosing_decl.timestamp_body = 1
                if enclosing_decl.ref_count == 0:
                    removable_decls.add(enclosing_decl.name)

    # count references from candidates to other declarations
    for info in candidates:
        info.outgoing_refs = 0
        candidate_text = "\n".join(lines[info.start_line:info.end_line+1])
        decl = info.enclosing_decl
        for other_decl in declarations.keys():
            if other_decl == decl.name:
                continue
            pattern = decl_patterns[other_decl]
            c_cand = len(pattern.findall(candidate_text))
            info.outgoing_refs += c_cand

    # Reorder candidates by topological order if enabled, as well as outgoing refs
    if use_topological_order:
        topo_order = compute_topological_order(declarations, dependencies)
        log(f"Topological order of declarations: {topo_order}", level=2)
        #print declaration names with scc_ids
        for decl_name in topo_order:
            decl = declarations[decl_name]
            log(f"  Decl: {decl.name}, SCC ID: {decl.scc_id}", level=2)
        candidates = _reorder_candidates_by_topological_order(candidates, topo_order)
        # print the reordered candidates for debugging
        log("Reordered candidates by topological order:", level=2)
        for info in candidates:
            decl_name = info.enclosing_decl.name if info.enclosing_decl else "Global"
            log(f"  Candidate ID {info.id}: lines {info.start_line+1}-{info.end_line+1}, Decl: {decl_name}, Loc: {info.enclosing_location}", level=2)   

    # renumber candidate ids
    for new_id, info in enumerate(candidates):
        info.id = new_id

    return FileStructure(
        lines=lines,
        candidates=candidates,
        declarations=declarations,
        contains_negative_tests=contains_negative_tests,
        decls_with_negative_tests=decls_with_negative_tests,
        dependencies=dependencies,
        deps_spec=deps_spec,
        deps_body=deps_body,
        removable_decls=removable_decls
    )


def _reorder_candidates_by_topological_order(
    candidates: list[RemovalCandidate],
    topo_order: list[str]
) -> list[RemovalCandidate]:
    """
    Reorder candidates so they follow topological order of declarations.

    Since we iterate backwards through candidates, leaf declarations (which
    should be processed first) need to be at the END of the list. The
    topo_order has leaves first, so we reverse it for candidate placement.

    Order after reordering:
    1. Global candidates (no enclosing declaration) - at the beginning
    2. Candidates from root declarations (many dependents)
    3. ...
    4. Candidates from leaf declarations (no dependents) - at the end

    Within each declaration, the original order is preserved within each section.

    Args:
        candidates: Original list of candidates.
        topo_order: Topological order of declarations (leaves first).

    Returns:
        Reordered list of candidates.
    """

    # Group candidates by declaration name
    by_decl: dict[Optional[str], list[RemovalCandidate]] = defaultdict(list)
    by_decl_loc: dict[Optional[str], dict[str, list[RemovalCandidate]]] = defaultdict(lambda: defaultdict(list))
    for candidate in candidates:
        decl_name = candidate.enclosing_decl.name if candidate.enclosing_decl else None
        by_decl[decl_name].append(candidate)
        if reverse_decl_sections:
            location = candidate.enclosing_location
            by_decl_loc[decl_name][location].append(candidate) 
    
    # Build reordered list
    reordered = []

    # 1. Global candidates first (will be processed last when iterating backwards)
    if None in by_decl:
        reordered.extend(by_decl[None])

    # 2. Declarations in topological order
    for decl_name in topo_order:
        if decl_name in by_decl:
            if reverse_decl_sections:
                for loc in ["B", "S", "H", None]:
                    if loc in by_decl_loc[decl_name]:
                        reordered.extend(sorted(by_decl_loc[decl_name][loc], key=lambda c: c.outgoing_refs))
            else:
                reordered.extend(by_decl[decl_name])

    # 3. Any declarations not in topo_order (shouldn't happen, but be safe)
    seen = set(topo_order) | {None}
    for decl_name, cands in by_decl.items():
        if decl_name not in seen:
            reordered.extend(cands)

    return reordered


def _find_sccs(nodes: set[str], graph: dict[str, set[str]]) -> list[list[str]]:
    """
    Find strongly connected components using Tarjan's algorithm.

    Args:
        nodes: Set of node names.
        graph: Adjacency list (node -> set of neighbors).

    Returns:
        List of SCCs, each SCC is a list of node names.
        SCCs are returned in reverse topological order (sinks first).
    """
    index_counter = [0]
    stack = []
    lowlinks = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(node):
        index[node] = index_counter[0]
        lowlinks[node] = index_counter[0]
        index_counter[0] += 1
        stack.append(node)
        on_stack[node] = True

        for neighbor in graph.get(node, set()):
            if neighbor not in index:
                strongconnect(neighbor)
                lowlinks[node] = min(lowlinks[node], lowlinks[neighbor])
            elif on_stack.get(neighbor, False):
                lowlinks[node] = min(lowlinks[node], index[neighbor])

        # If node is a root of an SCC
        if lowlinks[node] == index[node]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == node:
                    break
            sccs.append(scc)

    for node in nodes:
        if node not in index:
            strongconnect(node)

    return sccs


def compute_topological_order(declarations: dict[str, DeclarationInfo], dependencies: dict[tuple[str, str], int]) -> list[str]:
    """
    Compute topological order of declarations for processing (leaves first).
    Also assigns SCC IDs to DeclarationInfo objects.

    Uses Tarjan's algorithm to find strongly connected components (SCCs),
    then topologically sorts SCCs so that declarations with no dependents
    (leaf nodes) come first. This allows us to fully simplify leaf
    declarations before moving to their callers, avoiding wasted
    verification attempts on code that will be removed later.

    Tie-breaking: When multiple declarations/SCCs have the same topological
    level, they are sorted by descending header_start position (declarations
    later in the file come first).

    Args:
        declarations: Map from declaration name to DeclarationInfo.
        dependencies: Map of dependencies {(A, B): count} where A depends on B.

    Returns:
        List of declaration names in topological order (leaves first).
    """
    decl_names = set(declarations.keys())

    if not decl_names:
        return []

    # Build reverse dependency map: for each decl, who depends on it
    # dependencies has (A, B) -> count meaning A depends on B
    # So B's dependents include A
    dependents = defaultdict(set)  # B -> {A: A depends on B}

    for (a, b), _ in dependencies.items():
        if a in decl_names and b in decl_names:
            dependents[b].add(a)

    # Find SCCs using Tarjan's algorithm
    # We use the "dependents" graph direction: edges from B to A when A depends on B
    # This gives us SCCs in reverse topological order (leaves first)
    sccs = _find_sccs(decl_names, dependents)

    # Build SCC lookup: node -> SCC index
    scc_of = {}
    for scc_idx, scc in enumerate(sccs):
        for node in scc:
            scc_of[node] = scc_idx
            # each node is a declaration name; so updates each declaration to its scc index
            if node is not None and node in declarations:
                declarations[node].scc_id = scc_idx

    # Build condensation graph (DAG of SCCs) using dependents direction
    # scc_dependents[scc_i] = {scc_j: scc_j has nodes depending on nodes in scc_i}
    scc_dependents = defaultdict(set)
    for node in decl_names:
        node_scc = scc_of[node]
        for dep in dependents.get(node, set()):
            dep_scc = scc_of[dep]
            if dep_scc != node_scc:
                scc_dependents[node_scc].add(dep_scc)

    # Compute in-degree for SCCs (how many other SCCs depend on this one)
    scc_in_degree = {i: 0 for i in range(len(sccs))}
    for scc_idx, deps in scc_dependents.items():
        for dep_scc in deps:
            scc_in_degree[dep_scc] += 1

    # Helper to get sort key for an SCC (max header_start, descending)
    def scc_sort_key(scc_idx):
        return max(declarations[name].header_start for name in sccs[scc_idx])

    # Kahn's algorithm on SCCs with tie-breaking by descending header_start
    # Use a list as priority queue, sorted by descending max header_start
    ready = [i for i in range(len(sccs)) if scc_in_degree[i] == 0]
    ready.sort(key=scc_sort_key, reverse=True)

    result = []
    while ready:
        # Pop SCC with highest header_start (last in file)
        scc_idx = ready.pop()

        # Sort nodes within SCC by descending header_start
        scc_nodes = sorted(
            sccs[scc_idx],
            key=lambda name: declarations[name].header_start,
            reverse=True
        )
        result.extend(scc_nodes)

        # Update in-degrees and add newly ready SCCs
        for dep_scc in scc_dependents.get(scc_idx, set()):
            scc_in_degree[dep_scc] -= 1
            if scc_in_degree[dep_scc] == 0:
                # Insert maintaining sorted order (descending by header_start)
                # Binary search would be faster but list is typically small
                ready.append(dep_scc)
                ready.sort(key=scc_sort_key, reverse=True)

    return result


# ==============================================================================
# Incremental Update After Removal
# ==============================================================================


def update_after_removal(fs: FileStructure,
                         enclosing_decl: DeclarationInfo,
                         enclosing_location: str,
                         timestamp: int,
                         removed_segments: list[tuple[int, int, str]],
                         removed_code: str,
                         inserted_code: str,
                         new_lines: list[str]) -> None:
    """
    Incrementally update the FileStructure after successfully removing lines.

    This function maintains the FileStructure in a consistent state without
    requiring a full re-parse. It updates:
    - Line numbers in all RemovalCandidate and DeclarationInfo objects
    - Dependency counts (decremented for removed calls)
    - Timestamps for affected declarations and their neighbors
    - The set of declarations eligible for full removal

    Args:
        fs: The file structure to update (modified in place).
        enclosing_decl: Declaration containing the removed code (or None if global).
        enclosing_location: "H" (header), "S" (spec), "B" (body) or None (global).
        timestamp: Current logical timestamp for change tracking.
        removed_segments: List of (start, end, replacement) tuples that were removed (with eventual replacements).
        removed_code: The actual source code that was removed (for decrementing reference counts).
        new_lines: The new list of lines after removal.
    """
    # identify (semi)silent removals, without impact
    silent_removal = False
    postcond_removal = False
    if (len(removed_segments) == 1
        and removed_segments[0][0] == removed_segments[0][1]):
        line = fs.lines[removed_segments[0][0]].strip()
        if  line.startswith("decreases") or line.startswith("reads") or line.startswith("modifies"):
            silent_removal = True
        elif line.startswith("ensures"):
            postcond_removal = True

    # update timestamps in enclosing declaration on success for rechecking
    if enclosing_decl is not None and not silent_removal:
        if enclosing_location == "H":
            enclosing_decl.timestamp_body = timestamp
            enclosing_decl.timestamp_spec = timestamp
            # also delete from removable_decls
            fs.removable_decls.discard(enclosing_decl.name)
        elif enclosing_location == "S":
            enclosing_decl.timestamp_spec = timestamp
            # After removing a postcondition, body may have removable assertions
            # that were only needed to prove that postcondition
            if postcond_removal:
                enclosing_decl.timestamp_body = timestamp
        elif enclosing_location == "B":
            enclosing_decl.timestamp_body = timestamp
            enclosing_decl.timestamp_spec = timestamp

    # Update candidates list - ensure positions match between candidates and lines
    new_candidates = []
    for _, old in enumerate(fs.candidates):
        # adjust line numbers
        new_start, new_end, new_replace_with = update_segment_after_removals((old.start_line, old.end_line, old.replace_with), removed_segments)
        if new_start > new_end:
            continue
        # append adjusted info
        updated = RemovalCandidate(
            id=old.id,
            start_line=new_start,
            enclosing_location=old.enclosing_location,
            enclosing_decl=old.enclosing_decl,
            end_line=new_end,
            replace_with=new_replace_with,
            timestamp_last_attempt=old.timestamp_last_attempt,
            num_attempts=old.num_attempts,
            max_attempts=old.max_attempts,
            num_batch_attempts=old.num_batch_attempts
        )
        new_candidates.append(updated)

    # Update line numbers in declarations dictionary
    for decl in fs.declarations.values():
        new_header_start, new_body_end, _ = update_segment_after_removals((decl.header_start, decl.end_line, None), removed_segments)
        new_body_start, new_body_end, _ = update_segment_after_removals((decl.body_start, decl.end_line, None), removed_segments)
        if new_header_start > new_body_end: # to be removed
            decl.header_start = -1
            decl.body_start = -1
            decl.end_line = -1
        else:
            decl.header_start = new_header_start
            decl.body_start = new_body_start
            decl.end_line = new_body_end

    # update reference counters in dependencies
    if enclosing_decl is not None:
        for other_decl in fs.declarations.keys():
            if other_decl == enclosing_decl.name or other_decl not in removed_code:
                continue
            # Check if it is actually a call with parenthesis
            pattern = rf'\b{other_decl}\s*\('
            count = len(re.findall(pattern, removed_code))
            if inserted_code is not None and inserted_code != "":
                count -= len(re.findall(pattern, inserted_code))
            if count == 0:
                continue
            key = (enclosing_decl.name, other_decl)
            fs.dependencies[key] = fs.dependencies.get(key, 0) - count
            log(f"Decrementing dependency: {key} by {count}, new count: {fs.dependencies[key]}", level=2)
            # Also update fine-grained dependency dicts based on location
            if enclosing_location == "S":
                fs.deps_spec[key] = fs.deps_spec.get(key, 0) - count
            elif enclosing_location == "B":
                fs.deps_body[key] = fs.deps_body.get(key, 0) - count
            decl_info = fs.declarations.get(other_decl)
            decl_info.ref_count = max(0, decl_info.ref_count - count)
            if decl_info.ref_count == 0:
                fs.removable_decls.add(other_decl)
                log(f"{other_decl}: Marked for full removal due to 0 dependencies")

    # update neighbours timestamps in dependencies
    if enclosing_decl is not None and not silent_removal:
        for (a, b), _ in fs.dependencies.items():
            if a == enclosing_decl.name:
                b_info = fs.declarations.get(b)
                b_info.timestamp_spec = timestamp # to recheck spec (might need less ensures)
            if b == enclosing_decl.name and enclosing_location == "S": #and not postcond_removal:
                a_info = fs.declarations.get(a)
                # If A's spec references B, retry A's spec minimization (e.g., reduce requires)
                if (a, b) in fs.deps_spec:
                    a_info.timestamp_spec = timestamp
                    a_info.timestamp_body = timestamp
                # If A's body references B, retry A's body minimization (e.g., reduce asserts)
                if (a, b) in fs.deps_body:
                    a_info.timestamp_body = timestamp
                    a_info.timestamp_spec = timestamp

    # remove declaration if fully removed (and dependencies where it appears)
    if enclosing_location == "H":
        fs.declarations.pop(enclosing_decl.name, None)
        for (a, b), _ in list(fs.dependencies.items()):
            if a == enclosing_decl.name or b == enclosing_decl.name:
                fs.dependencies.pop((a, b), None)
        for (a, b), _ in list(fs.deps_spec.items()):
            if a == enclosing_decl.name or b == enclosing_decl.name:
                fs.deps_spec.pop((a, b), None)
        for (a, b), _ in list(fs.deps_body.items()):
            if a == enclosing_decl.name or b == enclosing_decl.name:
                fs.deps_body.pop((a, b), None)

    # update lines and candidates in fs
    fs.lines = new_lines
    fs.candidates = new_candidates


# ==============================================================================
# Segment Manipulation Utilities (start_line, end_line, replacement)
# This is needed because multiple overlapping, contiguous or unordered removal
# segments can be applied in a batch.
# ==============================================================================


def add_removal_segment(segments: list[tuple[int, int, str]], new_seg: tuple[int, int, str]) -> list[tuple[int, int, str]]:
    """
    Add a segment to an ordered list of non-overlapping and non-contiguous removal segments.

    Handles merging with adjacent or overlapping existing segments.

    Args:
        segments: Existing list of (start, end, replacement) tuples, sorted by start.
        new_seg: New segment (start, end, replacement) to add.

    Returns:
        Updated list with the new segment merged in.
    """
    i, j, ins = new_seg
    # skip previous segments
    pos = 0
    while pos < len(segments) and segments[pos][1] < i - 1:
        pos += 1
    # simple appending
    if pos == len(segments):
        segments.append(new_seg)
        return segments
    # simple insertion
    if j < segments[pos][0] - 1:
        segments.insert(pos, new_seg)
        return segments
    # adjacent or overlapping segments - extend and possibly merge existing segments
    start = min(i, segments[pos][0])
    end = max(j, segments[pos][1])
    if segments[pos][0] < i or (segments[pos][0] == i and segments[pos][1] > j):
        ins = segments[pos][2] # prevails replacement for larger segment
    pos_end = pos+1
    while pos_end < len(segments) and segments[pos_end][0] <= end-1:
        end = max(end, segments[pos_end][1])
        pos_end += 1
    # merge segments
    segments[pos:pos_end] = [(start, end, ins)]
    return segments


def update_segment_after_removals(seg: tuple[int, int, str], segments: list[tuple[int, int, str]]) -> tuple[int, int, str]:
    """
    Compute new line numbers for a segment after applying removals.

    Args:
        seg: Original segment as a tuple (start line, end line, replacement text).
        segments: List of removed segments (start, end, replacement).

    Returns:
        Tuple of (new_start, new_end, replacement).
        If new_start > new_end, the segment was fully removed.
    """
    old_i, old_j, old_repl = seg
    shift_i = 0
    shift_j = 0
    for (a, b, ins) in segments:
        if old_j < a:
            break
        elif old_i > b:
            shift_i += (b - a + 1)
            shift_j += (b - a + 1)
            if ins is not None:
                shift_i -= 1
                shift_j -= 1
        elif old_i >= a and old_j <= b: # fully removed or replaced
            if a == old_i and b == old_j and ins is not None and old_repl is None:
                return old_i-shift_i, old_i-shift_i+1, old_repl 
            else:
                return old_i-shift_i, old_i-shift_i-1, None  # fully removed/replaced
        elif old_i >= a:
            old_i = b + 1 # move i past removed segment
            shift_i += (b - a + 1)
            shift_j += (b - a + 1)
            if ins is not None:
                shift_i -= 1
                shift_j -= 1
        elif old_j <= b:
            old_j = a - 1 # move j before removed segment
            if ins is not None:
                old_j += 1
            break
        else: # removed in the middle, only j will be shifted
            shift_j += (b - a + 1)
            if ins is not None:
                shift_j -= 1

    return old_i-shift_i, old_j-shift_j, old_repl


def normalize_removal_segments(initial_list: list[tuple[int, int, str]]) -> list[tuple[int, int, str]]:
    """
    Normalize a list of removal segments by merging overlapping/adjacent ones.

    Args:
        initial_list: List of potentially overlapping (start, end, replacement) tuples.

    Returns:
        Sorted list of non-overlapping, non-adjacent segments.
    """
    normalized = []
    for seg in initial_list:
        normalized = add_removal_segment(normalized, seg)
    return normalized


# ==============================================================================
# Candidate Evaluation and Application
# ==============================================================================


def worth_try_removal(fs: FileStructure, info: RemovalCandidate, timestamp: int, batch: bool, round_num: int = 1) -> bool:
    """
    Determine if a removal candidate is worth attempting.

    Uses timestamps to avoid re-trying removals that haven't been affected
    by recent changes. A removal is worth trying if:
    - It hasn't exceeded its maximum attempt limit
    - Something has changed since the last attempt (timestamp check)
    - For declarations: they have no remaining references

    Args:
        fs: Current file structure.
        info: The candidate to evaluate.
        timestamp: Current logical timestamp.
        batch: True if this is part of a batch removal attempt.
        round_num: Current simplification round (reserved for future use).

    Returns:
        True if the removal should be attempted, False to skip.
    """
    last = info.timestamp_last_attempt

    if info.max_attempts != -1 and info.num_attempts >= info.max_attempts:
        recheck = False
    elif batch and info.num_batch_attempts >= max_batch_attempts:
        recheck = False
    elif info.enclosing_decl is None:
        recheck = last < timestamp
    elif info.enclosing_location  == "H":
        recheck = (info.enclosing_decl.ref_count <= 0) and (last < timestamp)
    elif info.enclosing_location == "B":
        recheck = last < info.enclosing_decl.timestamp_body
    elif info.enclosing_location == "S":
        recheck = last < info.enclosing_decl.timestamp_spec
    else:
        recheck = last < timestamp  # fallback


    if not recheck and verbose >=2:
        start_index = info.start_line
        end_index = info.end_line if info.end_line >= start_index else start_index
        remove_segment = "\n".join(fs.lines[start_index:end_index+1])
        log(f"{info.enclosing_decl.name}: skipped: {remove_segment}", level=2)

    return recheck


def apply_removal_segments(lines: list[str], segments: list[tuple[int, int, str]]) -> tuple[list[str], str]:
    """
    Apply removal segments to produce new lines and extract removed code.

    Args:
        lines: Original list of lines.
        segments: Normalized list of (start, end, replacement) segments to remove.

    Returns:
        Tuple of (new_lines, removed_code) where removed_code is the
        concatenation of all removed lines (for dependency analysis).
    """
    new_lines = []
    removed_parts = []
    current = 0
    inserted_parts = []

    for (i, j, ins) in segments:
        new_lines.extend(lines[current:i])
        if ins is not None:
            new_lines.append(ins)
            inserted_parts.append(ins)
        removed_parts.append("\n".join(lines[i:j+1]))
        current = j + 1

    new_lines.extend(lines[current:])
    removed_code = "\n".join(removed_parts) + "\n" if removed_parts else ""
    inserted_code = "\n".join(inserted_parts) + "\n" if inserted_parts else ""
    return new_lines, removed_code, inserted_code


def check_removal(fs: FileStructure, info_idxs: list[int], verification_cache: dict,
                  timestamp: int, 
                  profile_stats: ProfileStats = None) -> tuple[int, list[tuple[int, int, str]], str, str, list[str]]:
    """
    Attempt to remove one or more candidates and verify the result.

    This is the core function that:
    1. Computes the segments to remove from the candidate indices
    2. Generates the modified file content
    3. Verifies the modified file using Dafny
    4. Returns success/failure with the removal details

    Args:
        fs: Current file structure.
        info_idxs: Indices into fs.candidates of candidates to remove together.
        verification_cache: Cache mapping content hash to verification result.
        timestamp: Current logical timestamp.
        round_num: Current simplification round (affects timeout).
        profile_stats: Optional ProfileStats instance for metrics.

    Returns:
        Tuple of (removed_count, segments, removed_code, inserted_code, new_lines) where:
        - removed_count: Number of lines removed (0 if verification failed)
        - segments: List of (start, end, replacement) that were removed
        - removed_code: The actual code that was removed
        - inserted_code: The actual code that was inserted to replace removed code
        - new_lines: The new file lines after removal
    """
    # determine list of removal segments (i, j)
    removal_segments = [(fs.candidates[idx].start_line, fs.candidates[idx].end_line, fs.candidates[idx].replace_with) for idx in info_idxs]

    # normalize removal segments
    removal_segments = normalize_removal_segments(removal_segments)

    # determine new lines and removed code
    new_lines, removal_code, inserted_code = apply_removal_segments(fs.lines, removal_segments)

    # get enclosing declaration from first info (should be the same for all)
    enclosing_decl = fs.candidates[info_idxs[0]].enclosing_decl
    enclosing_location = fs.candidates[info_idxs[0]].enclosing_location

    # count lines removed, comparing new_lines with fs.lines
    removal_count = len(fs.lines) - len(new_lines)

    # marke new attempt and check if need verification
    # keep track of maximum number of attempts for these candidates
    num_attempts = 0
    need_verify = False
    for info_idx in info_idxs:
        info = fs.candidates[info_idx]
        info.num_attempts += 1
        num_attempts = max(num_attempts, info.num_attempts)
        if not (info.start_line == info.end_line and fs.lines[info.start_line].strip().startswith("//")):
            need_verify = True

    # in case of a batch, do not update timestamp of last attempt (to enable individual retries)
    if len(info_idxs) == 1:
        info = fs.candidates[info_idxs[0]]
        info.timestamp_last_attempt = timestamp
    else: # mark as batch attempt counter
        for info_idx in info_idxs:
            info = fs.candidates[info_idx]
            info.num_batch_attempts += 1

    # Check if the simplified file passes verification
    # (Skip verification for comment-only removals)
    if need_verify:
        contents="\n".join(new_lines)
        filter_symbol = None
        if use_filter_symbol and enclosing_decl is not None:
            if enclosing_decl.kind == "M" and enclosing_location == "B":
                filter_symbol = enclosing_decl.name
        # Check cache
        key = sha1(contents.encode("utf-8")).hexdigest()
        if verification_cache is not None and key in verification_cache:
            cached = True
            success = verification_cache[key]  # cached result
            duration = 0.0

            # Record profiling stats for cached verification
            if profile_stats:
                profile_stats.add_verification(duration, success, cached=True)
        else:
            cached = False
            # Negative tests only need re-verification when a spec change affects
            # a declaration that a test method with negative tests depends on.
            # This avoids redundant negative test checks for body changes or
            # changes to declarations that no negative test depends on.
            handle_neg_tests = False
            if fs.contains_negative_tests and enclosing_location == "S" and enclosing_decl is not None:
                # Check if any test with negative tests depends on this declaration
                for test_name in fs.decls_with_negative_tests:
                    if test_name == enclosing_decl.name or (test_name, enclosing_decl.name) in fs.dependencies:
                        handle_neg_tests = True
                        break

            # if marked for removal, can retry with longer timeout
            timeout = verifier_timeout + num_attempts - 1
            if enclosing_location == "H" and enclosing_decl is not None:
                timeout = timeout * 2
            timeout = min(timeout, max_verifier_timeout)

            # Verify the simplified file (returns success code and duration)
            success, duration, _ = verify_dafny_file(contents,
                                        new_lines,
                                        handle_negative_tests=handle_neg_tests,
                                        filter_symbol=filter_symbol,
                                        timeout=timeout,
                                        profile_stats=profile_stats)

            # Record profiling stats for actual verification
            if profile_stats:
                profile_stats.add_verification(duration, success, cached=False)

            # Log timing for slow verifications
            if duration > timeout:
                log(f"  Verification took {duration:.1f}s", level=2)

            # Put results in a cache from file contents to result
            if verification_cache is not None:
                verification_cache[key] = success
    else:
        cached = False
        success = 1  # trivially passes
        duration = 0.0

    # skip removal candidate if didn't pass verification
    name = enclosing_decl.name if enclosing_decl is not None else "Global"
    if success != 1:
        cache_msg = " (using cache)" if cached else ""
        ins_msg = f" to be replaced with: {inserted_code}" if inserted_code != "" else ""
        log(f"{name}({enclosing_location})({num_attempts}): kept{cache_msg}: {removal_code}{ins_msg}", level=1)
        removal_count = 0
    else:
        if inserted_code != "":
            log(f"{name}({enclosing_location})({num_attempts}): replaced: {removal_code}  with: {inserted_code}")
        else:
            log(f"{name}({enclosing_location})({num_attempts}): removed: {removal_code}")

    return removal_count, removal_segments, removal_code, inserted_code, new_lines


def find_removable_declaration_info(fs: FileStructure, timestamp: int) -> int:
    """
    Find a declaration that can be fully removed (no remaining references).

    Prioritizes removing entire declarations when they become unreferenced,
    as this is more efficient than removing their contents line by line.

    Args:
        fs: Current file structure.
        timestamp: Current logical timestamp.

    Returns:
        Index into fs.candidates of the declaration's header, or -1 if none found.
    """
    if fs.removable_decls is not None:
        for decl_name in fs.removable_decls:
            decl_info = fs.declarations[decl_name]
            for idx, candidate in enumerate(fs.candidates):
                if candidate.enclosing_decl == decl_info and candidate.enclosing_location == "H":
                    if candidate.timestamp_last_attempt < timestamp:
                        return idx
                    else:
                        break
    return -1


# ==============================================================================
# Main Simplification Functions
# ==============================================================================


def simplify_file(original_file: str, modified_file: str, simplified_file: str,
             start_from_simplified_file: bool = False,
             worker_id: str = None) -> tuple[int, ProfileStats]:
    """
    Simplify a Dafny file by removing unnecessary lines while preserving verification.

    This is the main entry point for simplifying a single file. The algorithm:
    1. Preprocesses the file to identify removable candidates
    2. Iterates through candidates, attempting removal from end to start
    3. For each candidate, verifies the modified file still passes
    4. Repeats in rounds until no more removals are possible

    The function uses several optimizations:
    - Single preprocessing pass (no re-parsing after each removal)
    - Incremental verification using --filter-symbol where applicable
    - Caching to avoid duplicate verifications
    - Batch removal attempts to reduce verification calls
    - Timestamp-based tracking to skip unchanged candidates

    Args:
        original_file: Path to the original (stripped) Dafny file.
        modified_file: Path to the modified file to simplify.
        simplified_file: Path where the simplified output will be written.
        start_from_simplified_file: If True, continue from existing simplified
            file instead of the modified file.
        worker_id: Optional worker identifier for log messages.

    Returns:
        Tuple of (lines_removed, profile_stats).
    """
    # Create per-file profiling stats
    file_profile_stats = ProfileStats() if enable_profiling else None

    # Read original file
    with open(original_file, 'r', encoding='utf-8') as file:
        original_content = file.read()

    # Read modified file
    with open(modified_file, 'r', encoding='utf-8') as file:
        modified_content = file.read()

    # Read current simplified file, if existent
    simplified_content = None
    if os.path.exists(simplified_file):
        with open(simplified_file, 'r', encoding='utf-8') as file:
            simplified_content = file.read()

    # If starting from simplified file, use its content
    if start_from_simplified_file:
        if simplified_content is not None:
            modified_content = simplified_content
        else:
            log(f"Could not find simplified file {simplified_file} to start from.")
            return 0, file_profile_stats
    
    # Preprocess the file structure ONCE (this analyzes everything upfront)
    original_lines = original_content.splitlines()
    modified_lines = modified_content.splitlines()

    if enable_profiling:
        preprocess_start = time.time()
    file_structure = preprocess_file(modified_lines, original_lines)
    if enable_profiling:
        file_profile_stats.preprocessing_time = time.time() - preprocess_start
        log(f"  Preprocessing took {file_profile_stats.preprocessing_time:.2f}s")

    # Print declarations found
    log(f"  Preprocessed: {len(file_structure.declarations)} declarations found", level=2)
    if verbose >= 2:
        for _, decl in file_structure.declarations.items():
            log(f"    - {decl.name}: header={decl.header_start+1}, body={decl.body_start+1}, end={decl.end_line+1}, timestamp_spec={decl.timestamp_spec}, timestamp_body={decl.timestamp_body}, ref_count={decl.ref_count}", level=2)

    # Print dependencies found
    if verbose >= 2:
        log("  Declaration dependencies:", level=2)
        for (dependent, dependee), count in file_structure.dependencies.items():
            log(f"    - {dependent} depends on {dependee}: {count} times", level=2)

    # Print candidates found
    if verbose >= 2:
        log(f"  Preprocessed: {len(file_structure.candidates)} removal candidates found", level=2)
        for info in file_structure.candidates:
            start = info.start_line + 1
            end = info.end_line + 1
            loc = info.enclosing_location
            decl_name = info.enclosing_decl.name if info.enclosing_decl is not None else "Global"
            log(f"    - id {info.id} lines {start}-{end}, location={loc}, decl={decl_name}", level=2)

    # Initialize counters, cache, timestamp
    total_removed_count = 0
    round_num = 1
    verification_cache = {}  # map from sha1 of file contents to verification result
    timestamp = 1

    # Main simplification loop - multiple rounds until no more removals
    # Note: when use_topological_order is True, candidates are pre-sorted during
    # preprocessing so that iterating backwards processes leaf declarations first.
    while True:
        log(f"\n========== Round {round_num} ==========")

        # Count of removals this round
        round_removed_count = 0

        # Iterate through candidates backwards (leaf declarations are at the end when
        # topological ordering is enabled, so they get processed first)
        resume_at_info_id_after_removal = None
        last_modified_scc = None
        inner_round = 0
        k = len(file_structure.candidates)
        while k > 0 and k <= len(file_structure.candidates):
            # determine next k, giving priority to declarations to remove
            k -= 1

            # possible jump to next removable declaration
            rmv_k = find_removable_declaration_info(file_structure, timestamp)
            if rmv_k >= 0:
                # remember position after removal to resume
                if resume_at_info_id_after_removal is None:
                    resume_at_info_id_after_removal =  file_structure.candidates[k].id
                # jump to declaration removal
                k = rmv_k
            # possible resume after previous removal
            elif resume_at_info_id_after_removal is not None:
                for idx, candidate in enumerate(file_structure.candidates):
                    if candidate.id >= resume_at_info_id_after_removal:
                        k = idx
                        log(f"Resuming at candidate with id {candidate.id} after previous removal", level=2)
                        break
                resume_at_info_id_after_removal = None
            # Possibly continuation in the previous declaration (instead of moving to the next) if eligible candidates
            elif exhaust_declaration_removals and last_modified_scc is not None:
                info = file_structure.candidates[k]
                if info.enclosing_decl is None or info.enclosing_decl.scc_id != last_modified_scc:
                    log(f"Trying to continue in declaration {last_modified_scc}", level=2)
                    # go to the last candidate in the last modified declaration
                    while k+1 < len(file_structure.candidates):
                        next_info = file_structure.candidates[k+1]
                        if next_info.enclosing_decl is None or next_info.enclosing_decl.scc_id != last_modified_scc:
                            break
                        k += 1
                    log(f"Continuing at candidate id {file_structure.candidates[k].id} in declaration {file_structure.candidates[k].enclosing_decl.name if file_structure.candidates[k].enclosing_decl is not None else None}", level=2)
                    inner_round += 1
                    last_modified_scc = None

            # get candidate
            info = file_structure.candidates[k]
            candidate_id = info.id
            recheck = worth_try_removal(file_structure, info, timestamp, False, round_num)
            if not recheck:
                continue
            enclosing_decl = info.enclosing_decl
            enclosing_location = info.enclosing_location
            batch_list = [k]

            # possibly try several at once
            start = info.start_line
            stop = info.end_line
            if max_batch_size > 1 and info.enclosing_location == "B" and info.num_batch_attempts < max_batch_attempts and stop - start + 1 < max_batch_lines:
                idx = k-1
                while idx >= 0 and len(batch_list) < max_batch_size:
                    info2 = file_structure.candidates[idx]
                    if info2.enclosing_location != info.enclosing_location or info2.enclosing_decl != info.enclosing_decl:
                        break
                    # ignore if not adjacent
                    #if info2.end_line + 1 < start or info2.start_line > stop + 1:
                    #    break
                    start = min(info2.start_line, start)
                    stop = max(info2.end_line, stop)
                    if stop - start + 1 > max_batch_lines:
                        break
                    recheck = worth_try_removal(file_structure, info2, timestamp, True, round_num)
                    if recheck:
                        # add to batch_list
                        batch_list.append(idx)
                    idx -= 1


            # Check if removal can be done (successful verification)
            removed_count, removed_segments, removed_code, inserted_code, new_lines = check_removal(
                file_structure, batch_list, verification_cache, timestamp, file_profile_stats)
            if removed_count == 0:
                if len(batch_list) > 1:
                    k += 1 # retry individually
                continue  # could not remove

            # Last declaration name modified
            if enclosing_location != "H":
                last_modified_scc = info.enclosing_decl.scc_id if info.enclosing_decl is not None else None

            # Increment timestamp
            timestamp += 1

            # Update file structure
            update_after_removal(file_structure, enclosing_decl, enclosing_location, timestamp, removed_segments, removed_code, inserted_code, new_lines)

            # Update counters
            round_removed_count += removed_count

            # May cause removal of previous candidates (shifting others), so adjust k accordingly
            if k > len(file_structure.candidates):
                k = len(file_structure.candidates)
            while k > 0 and file_structure.candidates[k-1].id >= candidate_id:
                k -= 1

        # End of round - check if we made progress
        if round_removed_count == 0:
            log(f"Round {round_num}: No more simplifications possible.")
            break
        else:
            log(f"Round {round_num}: Removed {round_removed_count} lines.")
            total_removed_count += round_removed_count
            round_num += 1
            continue

    # Final cleanup
    if total_removed_count == 0:
        if not start_from_simplified_file:
            if os.path.exists(simplified_file):
                os.remove(simplified_file)
        else:
            with open(simplified_file, 'w', encoding='utf-8') as file:
                file.write("\n".join(file_structure.lines))
        return 0, file_profile_stats

    # Save the final simplified content
    with open(simplified_file, 'w', encoding='utf-8') as file:
        file.write("\n".join(file_structure.lines))

    log(f"\n========== COMPLETE ==========")
    log(f"Total rounds: {round_num}")
    log(f"Total lines removed: {total_removed_count}")

    return total_removed_count, file_profile_stats


def _simplify_file_worker(args: tuple) -> tuple[str, int, float, ProfileStats]:
    """
    Worker function for parallel file processing.

    Args:
        args: Tuple of (original_file, modified_file, simplified_file,
              start_from_simplified, worker_id)

    Returns:
        Tuple of (filename, lines_removed, elapsed_time, profile_stats)
    """
    original_file, modified_file, simplified_file, start_from_simplified, worker_id = args

    filename = os.path.basename(modified_file)
    log(f"\n{'='*60}")
    log(f"[Worker {worker_id}] Simplifying {filename}")
    log(f"{'='*60}")

    start_time = time.time()

    try:
        removed_lines, profile_stats = simplify_file(
            original_file,
            modified_file,
            simplified_file,
            start_from_simplified_file=start_from_simplified,
            worker_id=worker_id
        )
        elapsed = time.time() - start_time
        return (filename, removed_lines, elapsed, profile_stats)
    except Exception as e:
        elapsed = time.time() - start_time
        log(f"[Worker {worker_id}] Error processing {filename}: {e}")
        return (filename, -1, elapsed, None)


def simplify_folder(folder_with_stripped_files: str, folder_with_modified_files: str,
                    folder_with_simplified_files: str,
                    start_from_simplified_files: bool = False,
                    parallel_workers: int = None) -> tuple[int, int]:
    """
    Batch simplify all Dafny files in a folder.

    Processes all files matching the pattern "*_NN_llm.dfy" in the modified folder,
    using corresponding "*_stripped.dfy" files as originals.

    File naming convention:
    - Original: {base}_stripped.dfy
    - Modified: {base}_NN_llm.dfy (where NN is a number)
    - Output: {base}_NN_llm_simplified.dfy

    Args:
        folder_with_stripped_files: Folder containing original *_stripped.dfy files.
        folder_with_modified_files: Folder containing *_llm.dfy files to simplify.
        folder_with_simplified_files: Folder where *_simplified.dfy outputs go.
        start_from_simplified_files: If True, continue from existing simplified files.
        parallel_workers: Number of parallel workers (default: use max_workers config).
            Set to 1 for sequential processing.

    Returns:
        Tuple of (files_simplified, total_lines_removed).
    """

    if parallel_workers is None:
        parallel_workers = max_workers

    # Collect all file jobs
    file_jobs = []
    for filename in os.listdir(folder_with_modified_files):
        if not filename.endswith('_llm.dfy'):
            continue

        match = re.match(r'^(.*)_\d+_llm\.dfy$', filename)
        if not match:
            log(f"Could not find stripped file for {filename}")
            continue

        base_name = match.group(1)
        stripped_filename = f"{base_name}_stripped.dfy"

        filepath_modified = os.path.join(folder_with_modified_files, filename)
        filepath_stripped = os.path.join(folder_with_stripped_files, stripped_filename)
        filepath_simplified = os.path.join(folder_with_simplified_files,
                                           filename.replace('_llm.dfy', '_llm_simplified.dfy'))

        if not os.path.exists(filepath_stripped):
            log(f"Stripped file not found: {filepath_stripped}")
            continue

        file_jobs.append((filepath_stripped, filepath_modified, filepath_simplified,
                         start_from_simplified_files))

    log(f"\nFound {len(file_jobs)} files to process with {parallel_workers} worker(s)")

    total_simplified_files = 0
    total_removed_lines = 0
    total_time_seconds = 0
    aggregated_stats = ProfileStats() if enable_profiling else None

    batch_start_time = time.time()

    if parallel_workers <= 1:
        # Sequential processing (same as v8)
        for i, job in enumerate(file_jobs):
            args = (*job, f"seq-{i}")
            filename, removed_lines, elapsed, profile_stats = _simplify_file_worker(args)

            total_time_seconds += elapsed

            if removed_lines > 0:
                log(f"\n{filename}: Simplified by removing {removed_lines} lines (time: {elapsed:.0f} seconds)")
                total_simplified_files += 1
                total_removed_lines += removed_lines
            elif removed_lines == 0:
                log(f"\n{filename}: Could not be simplified (time: {elapsed:.0f} seconds)")
            else:
                log(f"\n{filename}: Error during processing (time: {elapsed:.0f} seconds)")

            if enable_profiling and profile_stats:
                aggregated_stats.merge(profile_stats)
    else:
        # Parallel processing
        worker_args = [(job[0], job[1], job[2], job[3], f"p{i}")
                       for i, job in enumerate(file_jobs)]

        with ProcessPoolExecutor(max_workers=parallel_workers) as executor:
            futures = {executor.submit(_simplify_file_worker, args): args
                      for args in worker_args}

            for future in as_completed(futures):
                try:
                    filename, removed_lines, elapsed, profile_stats = future.result()

                    total_time_seconds += elapsed

                    if removed_lines > 0:
                        log(f"\n{filename}: Simplified by removing {removed_lines} lines (time: {elapsed:.0f} seconds)")
                        total_simplified_files += 1
                        total_removed_lines += removed_lines
                    elif removed_lines == 0:
                        log(f"\n{filename}: Could not be simplified (time: {elapsed:.0f} seconds)")
                    else:
                        log(f"\n{filename}: Error during processing (time: {elapsed:.0f} seconds)")

                    if enable_profiling and profile_stats:
                        aggregated_stats.merge(profile_stats)

                except Exception as e:
                    args = futures[future]
                    log(f"Error processing {args[1]}: {e}")

    batch_elapsed = time.time() - batch_start_time

    log(f"\n{'='*60}")
    log(f"BATCH COMPLETE")
    log(f"Total simplified files: {total_simplified_files}")
    log(f"Total removed lines: {total_removed_lines}")
    log(f"Total CPU time: {total_time_seconds/60:.1f} minutes")
    log(f"Wall clock time: {batch_elapsed/60:.1f} minutes")
    if parallel_workers > 1:
        log(f"Speedup: {total_time_seconds/batch_elapsed:.2f}x with {parallel_workers} workers")
    log(f"{'='*60}")

    # Print aggregated profiling summary
    if enable_profiling and aggregated_stats:
        aggregated_stats.print_summary()

    return total_simplified_files, total_removed_lines


# Main entry point
if __name__ == "__main__":
    simplify_folder(r"TODO", r"TODO", r"TODO")
