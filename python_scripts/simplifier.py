"""
Dafny Simplifier v8 - Automatic simplification of Dafny programs.

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
    - Batch removal attempts to reduce verification calls
    - Caching of verification results to avoid duplicate checks
    - Support for negative tests (marked with //@invalid)
    - Handles multi-line blocks (if, while, forall, calc, etc.)

Performance Optimizations (v8):
    - Reuses temporary file for verification (reduces file I/O overhead)
    - Early termination with subprocess.run timeout (prevents hanging)
    - Optimized regex patterns for brace counting (single pass)
    - Space-optimized LCS matching (O(n) instead of O(m*n) space)
    - Comprehensive profiling to identify bottlenecks

Usage:
    # Single file simplification:
    simplify_file("original.dfy", "modified.dfy", "output.dfy")

    # Batch processing of a folder:
    simplify_folder("stripped_folder", "modified_folder", "output_folder")

Author: João Pascoal Faria (jpf@fe.up.pt)
License: MIT License

Copyright (c) 2026 João Pascoal Faria

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""

from __future__ import annotations


# ==============================================================================
# Configuration Parameters
# ==============================================================================

# Path to the Dafny executable (full path, or just "dafny.exe" if in PATH)
dafny_executable = r"dafny.exe"

# Verbosity level:
#   0 = silent (no output)
#   1 = normal (progress and results)
#   2 = verbose (detailed debugging information)
verbose = 1

# Enable profiling to track time spent in different operations
enable_profiling = False

# Verification timeout settings (in seconds)
verifier_timeout = 10       # Initial timeout per verification call
max_verifier_timeout = 60   # Maximum timeout (used for retries and full declarations)

# Handle negative tests: programs with //@invalid markers that should fail verification
handle_negative_tests = True

# Use --filter-symbol to verify only the affected method/lemma (faster for body changes)
use_filter_symbol = True

# Group consecutive statements for batch removal before trying individual removal
optimize_sequence = True

# Batch removal settings: try removing multiple candidates at once
max_batch_size = 4    # Maximum number of candidates to batch together
max_batch_lines = 10  # Maximum total lines in a batch
max_batch_attempts = 1  # Number of batch attempts before falling back to individual


# ==============================================================================
# Imports
# ==============================================================================

import atexit
import os
import re
import subprocess
import tempfile
import time
from collections import defaultdict, deque
from dataclasses import dataclass
from hashlib import sha1
from typing import Optional


# ==============================================================================
# Logging
# ==============================================================================

# Create a timestamped log file for this session
_log_timestamp = time.strftime("%Y%m%d-%H%M%S")
log_file_path = f"simplifier_log_{_log_timestamp}.txt"
log_file = open(log_file_path, "w", encoding="utf-8")

# Ensure log file is properly closed on exit
atexit.register(lambda: log_file.close())


# ==============================================================================
# Profiling
# ==============================================================================


@dataclass
class ProfileStats:
    """Statistics for profiling verification performance."""
    total_verifications: int = 0
    successful_verifications: int = 0
    failed_verifications: int = 0
    cached_verifications: int = 0
    timeout_verifications: int = 0

    total_verification_time: float = 0.0
    min_verification_time: float = float('inf')
    max_verification_time: float = 0.0

    # Breakdown by location
    body_verifications: int = 0
    spec_verifications: int = 0
    header_verifications: int = 0

    body_verification_time: float = 0.0
    spec_verification_time: float = 0.0
    header_verification_time: float = 0.0

    # Other times
    preprocessing_time: float = 0.0

    def add_verification(self, duration: float, success: int, cached: bool, location: str = None):
        """Record a verification attempt."""
        if not cached:
            self.total_verifications += 1
            self.total_verification_time += duration
            self.min_verification_time = min(self.min_verification_time, duration)
            self.max_verification_time = max(self.max_verification_time, duration)

            if success == 1:
                self.successful_verifications += 1
            elif success == 0:
                self.failed_verifications += 1

            # Track by location
            if location == "B":
                self.body_verifications += 1
                self.body_verification_time += duration
            elif location == "S":
                self.spec_verifications += 1
                self.spec_verification_time += duration
            elif location == "H":
                self.header_verifications += 1
                self.header_verification_time += duration
        else:
            self.cached_verifications += 1

    def add_timeout(self):
        """Record a timeout."""
        self.timeout_verifications += 1

    def print_summary(self):
        """Print profiling summary."""
        print(f"\n{'='*60}")
        print(f"PROFILING SUMMARY")
        print(f"{'='*60}")

        print(f"\nVerification Calls:")
        print(f"  Total verifications: {self.total_verifications}")
        print(f"  Successful: {self.successful_verifications}")
        print(f"  Failed: {self.failed_verifications}")
        print(f"  Cached (skipped): {self.cached_verifications}")
        print(f"  Timeouts: {self.timeout_verifications}")

        if self.total_verifications > 0:
            avg_time = self.total_verification_time / self.total_verifications
            print(f"\nVerification Time:")
            print(f"  Total: {self.total_verification_time:.1f}s ({self.total_verification_time/60:.1f}m)")
            print(f"  Average: {avg_time:.2f}s")
            print(f"  Min: {self.min_verification_time:.2f}s")
            print(f"  Max: {self.max_verification_time:.2f}s")

            print(f"\nVerification Breakdown by Location:")
            if self.body_verifications > 0:
                avg_body = self.body_verification_time / self.body_verifications
                print(f"  Body: {self.body_verifications} calls, {self.body_verification_time:.1f}s total, {avg_body:.2f}s avg")
            if self.spec_verifications > 0:
                avg_spec = self.spec_verification_time / self.spec_verifications
                print(f"  Spec: {self.spec_verifications} calls, {self.spec_verification_time:.1f}s total, {avg_spec:.2f}s avg")
            if self.header_verifications > 0:
                avg_header = self.header_verification_time / self.header_verifications
                print(f"  Header: {self.header_verifications} calls, {self.header_verification_time:.1f}s total, {avg_header:.2f}s avg")

        if self.preprocessing_time > 0:
            print(f"\nOther Times:")
            print(f"  Preprocessing: {self.preprocessing_time:.2f}s")

        print(f"{'='*60}\n")

        # Also write to log file
        log_file.write(f"\n{'='*60}\n")
        log_file.write(f"PROFILING SUMMARY\n")
        log_file.write(f"{'='*60}\n")
        log_file.write(f"\nVerification Calls:\n")
        log_file.write(f"  Total verifications: {self.total_verifications}\n")
        log_file.write(f"  Successful: {self.successful_verifications}\n")
        log_file.write(f"  Failed: {self.failed_verifications}\n")
        log_file.write(f"  Cached (skipped): {self.cached_verifications}\n")
        log_file.write(f"  Timeouts: {self.timeout_verifications}\n")

        if self.total_verifications > 0:
            avg_time = self.total_verification_time / self.total_verifications
            log_file.write(f"\nVerification Time:\n")
            log_file.write(f"  Total: {self.total_verification_time:.1f}s ({self.total_verification_time/60:.1f}m)\n")
            log_file.write(f"  Average: {avg_time:.2f}s\n")
            log_file.write(f"  Min: {self.min_verification_time:.2f}s\n")
            log_file.write(f"  Max: {self.max_verification_time:.2f}s\n")

            log_file.write(f"\nVerification Breakdown by Location:\n")
            if self.body_verifications > 0:
                avg_body = self.body_verification_time / self.body_verifications
                log_file.write(f"  Body: {self.body_verifications} calls, {self.body_verification_time:.1f}s total, {avg_body:.2f}s avg\n")
            if self.spec_verifications > 0:
                avg_spec = self.spec_verification_time / self.spec_verifications
                log_file.write(f"  Spec: {self.spec_verifications} calls, {self.spec_verification_time:.1f}s total, {avg_spec:.2f}s avg\n")
            if self.header_verifications > 0:
                avg_header = self.header_verification_time / self.header_verifications
                log_file.write(f"  Header: {self.header_verifications} calls, {self.header_verification_time:.1f}s total, {avg_header:.2f}s avg\n")

        if self.preprocessing_time > 0:
            log_file.write(f"\nOther Times:\n")
            log_file.write(f"  Preprocessing: {self.preprocessing_time:.2f}s\n")

        log_file.write(f"{'='*60}\n\n")

# Global profiling stats
profile_stats = ProfileStats()


# ==============================================================================
# Dafny Verification
# ==============================================================================

# Persistent temporary file for Dafny verification (reused to reduce I/O overhead)
_temp_dafny_file = None
_temp_dafny_path = None


def _get_temp_dafny_file() -> str:
    """
    Get or create a persistent temporary file for Dafny verification.

    The file is reused across all verifications to reduce file system overhead.
    It is automatically cleaned up when the program exits.

    Returns:
        Path to the temporary .dfy file.
    """
    global _temp_dafny_file, _temp_dafny_path

    if _temp_dafny_file is None:
        # Create a named temporary file that persists
        _temp_dafny_file = tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.dfy',
            delete=False,
            encoding='utf-8'
        )
        _temp_dafny_path = _temp_dafny_file.name
        _temp_dafny_file.close()  # Close but don't delete

        # Register cleanup function to delete on exit
        atexit.register(_cleanup_temp_file)

    return _temp_dafny_path

def _cleanup_temp_file():
    """Clean up the temporary Dafny file on program exit."""
    global _temp_dafny_file, _temp_dafny_path

    if _temp_dafny_path and os.path.exists(_temp_dafny_path):
        try:
            os.unlink(_temp_dafny_path)
        except Exception:
            pass  # Ignore cleanup errors

def verify_dafny_file(contents: str, lines: list[str], handle_negative_tests: bool = handle_negative_tests,
                      filter_symbol: str = None, filter_lines: tuple[int, int] = None, timeout: int = verifier_timeout) -> tuple[int, float]:
    """
    Verifies a Dafny file using the Dafny verifier.

    Args:
        contents: The contents of the Dafny file
        lines: The lines of the Dafny file
        handle_negative_tests: Whether to run negative tests
        filter_symbol: Optional method/function name to filter verification (uses --filter-symbol)
        filter_lines: Optional pair of first and last line numbers to filter verification
        timeout: Verification timeout in seconds

    Returns:
        Tuple of (success_code, duration) where:
        - success_code: 1 if verification succeeds, 0 if verification fails, -1 if syntax errors
        - duration: time spent in verification (seconds)
    """
    verify_start = time.time()

    # Get persistent temporary file path
    temp_dafny_path = _get_temp_dafny_file()

    # Write to temporary file (overwrite previous content)
    with open(temp_dafny_path, 'w', encoding='utf-8') as file:
        file.write(contents)

    # Build command
    cmd = [
        dafny_executable,
        "verify",
        temp_dafny_path,
        f"--verification-time-limit:{timeout}",
        "--allow-warnings:true",
        "--cores", "2"
    ]
    if filter_symbol:
        cmd.append(f"--filter-symbol={filter_symbol}.")
    if filter_lines is not None:
        cmd.append(f"--filter-position={filter_lines[0]}-{filter_lines[1]}")

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
        duration = time.time() - verify_start
        if enable_profiling:
            profile_stats.add_timeout()
        if verbose >= 2:
            print(f"  Verification timed out after {process_timeout}s")
            log_file.write(f"  Verification timed out after {process_timeout}s\n")
        return 0, duration  # verification failed due to timeout

    # Remove errors regarding counter-examples
    cleaned = "\n".join(
        line for line in stdout.decode('utf-8').splitlines()
        if not line.startswith("Prover error")
    )

    # Check for errors in output
    if "resolution/type errors" in cleaned or "parse errors" in cleaned:
        duration = time.time() - verify_start
        return -1, duration  # syntax errors
    if not cleaned.endswith(' 0 errors'):
        duration = time.time() - verify_start
        return 0, duration  # verification failed

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
            # Call the verifier again on the new file (no filter for negative tests)
            success, _ = verify_dafny_file(new_content, lines, False, filter_symbol, filter_lines, verifier_timeout)
            # restore the old line and continue
            lines[index] = old_line
            # If passes, return failure
            if success == 1:
                duration = time.time() - verify_start
                return 0, duration  # failure

    duration = time.time() - verify_start
    return 1, duration  # success


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
        timestamp_spec: Timestamp of last change to specification (requires/ensures).
        timestamp_body: Timestamp of last change to the body.
        timestamp_spec_neighbors: Timestamp indicating when neighbors changed,
            requiring re-verification of this declaration's spec.
        timestamp_body_neighbors: Timestamp indicating when neighbors changed,
            requiring re-verification of this declaration's body.
        ref_count: Number of references to this declaration from other declarations.
    """
    name: str
    kind: str
    header_start: int
    body_start: int
    end_line: int
    timestamp_spec: int = 0
    timestamp_body: int = 0
    timestamp_spec_neighbors: int = 0
    timestamp_body_neighbors: int = 0
    ref_count: int = 0


@dataclass
class LineInfo:
    """
    Information about a removable candidate (line or block).

    Attributes:
        id: Unique identifier for this candidate.
        line_num: Starting line number (0-indexed).
        block_end: Ending line number (same as line_num for single lines).
        enclosing_decl: The declaration containing this line, if any.
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
    line_num: int
    block_end: int
    enclosing_decl: Optional[DeclarationInfo]
    enclosing_location: Optional[str]
    replace_with: Optional[str]
    timestamp_last_attempt: int = 0
    num_attempts: int = 0
    max_attempts: int = -1
    num_batch_attempts: int = 0


@dataclass
class FileStructure:
    """
    Preprocessed structure of a Dafny file.

    This structure is computed once during preprocessing and updated incrementally
    as lines are removed. It contains all information needed for efficient
    simplification without re-parsing the file.

    Attributes:
        lines: Current lines of the file.
        line_info: List of removable candidates.
        declarations: Map from declaration name to DeclarationInfo.
        contains_negative_tests: True if file has //@invalid markers.
        dependencies: Map (A, B) -> count where A calls/references B.
            Count > 0 means direct dependency, count = 0 means indirect (transitive).
        removable_decls: Set of declaration names that can be fully removed
            (no other declarations depend on them).
    """
    lines: list[str]
    line_info: list[LineInfo]
    declarations: dict[str, DeclarationInfo]
    contains_negative_tests: bool
    dependencies: dict[tuple[str, str], int]
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

    This is a fallback for when the fast subsequence matching fails (e.g., when
    lines were reordered). Uses O(n) space optimization instead of O(m*n).

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
                        if verbose >= 2:
                            print(f"  Added indirect dependency edge: {start} -> {nxt}")
                            log_file.write(f"  Added indirect dependency edge: {start} -> {nxt}\n")


    return result


# ==============================================================================
#  Parsing Utilities
# ==============================================================================

# Keywords that start a declaration (method, lemma, function, predicate)
DECLARATION_STARTERS = [
    "function", "predicate", "lemma", "method",
    "ghost function", "ghost predicate", "ghost lemma", "ghost method"
]

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
    if s.startswith(("method", "lemma", "ghost method", "ghost lemma")):
        return "M"
    if s.startswith(("function", "predicate", "ghost function", "ghost predicate")):
        return "F"
    return "?"


def _find_block_end(lines: list[str], start_index: int, brace_depths: list[int]) -> tuple[int, Optional[str]]:
    """
    Find the end of a brace-delimited block starting at start_index.

    Handles if/else chains by continuing past closing braces followed by "else".

    Args:
        lines: All lines of the file.
        start_index: Line where the block starts.
        brace_depths: Precomputed brace depth at each line.

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

    start_depth = brace_depths[start_index - 1] if start_index > 0 else 0
    target_depth = start_depth

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
            if "else" in line_to_check or (i < len(lines) - 1 and "else" in lines[i + 1]):
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
    brace_depths = []
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
        brace_depths.append(current_depth)

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
                        timestamp_spec_neighbors=0,
                        timestamp_body_neighbors=0,
                        ref_count=0
                    )
                    declarations[current_decl_name] = new_decl
                    current_decl_name = None
                    current_decl_header_start = -1
                    current_decl_body_start = -1
                    current_decl_kind = None


    # Compute LCS-based matching between modified and original lines
    modified_normalized = [normalize_line(line) for line in lines]
    lcs_matching = compute_subsequence_matching(modified_normalized, original_normalized)

    # Second pass: build line info with all preprocessed data
    line_infos = []
    # queue of line_info corresponding to start of blocks to be inserted later at end of block
    line_info_queue = deque()

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

        # Track if we need to add a second LineInfo for "assert...by" statements
        by_replace_with = None
        is_block_start = False
        code_part = stripped.split("//")[0].rstrip()

        # Check if this is a declaration start
        if enclosing_location == "H":
            block_end = enclosing_decl.end_line
        # Check if this starts a block
        elif any(code_part.startswith(token) for token in BLOCK_INITIATORS):
            block_end, replace_with = _find_block_end(lines, i, brace_depths)
            is_block_start = True
        elif code_part.startswith("assert ") and " by {" in code_part:
            # Assert with inline "by {" block - create TWO options:
            # 1. Remove entire statement (this LineInfo)
            # 2. Replace just the "by {...}" part with ";" (second LineInfo below)
            block_end, _ = _find_block_end(lines, i, brace_depths)
            if block_end > i:
                is_block_start = True
            # Prepare second option: replace "by {...}" with ";"
            by_replace_with = line[:line.find(" by {")] + ";"
        elif (code_part.startswith("assert ") or code_part.startswith("==")) and not code_part.endswith(";"):
            if code_part.startswith("assert ")  and i + 1 < len(lines) and lines[i + 1].strip().startswith("by "):
                block_end, _ = _find_block_end(lines, i, brace_depths)
                if block_end > i:
                    is_block_start = True
            else:
                block_end = _find_statement_end(lines, i)
        elif any(code_part.startswith(clause) for clause in CLAUSE_KEYWORDS):
            # Multiline clause - find the end of the clause
            block_end = _find_clause_end(lines, i)
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
            # For "assert...by" statements, add a second LineInfo for "replace by with ;" option
            if by_replace_with is not None:
                line_infos.append(LineInfo(
                    id=0,
                    line_num=i,
                    enclosing_decl=enclosing_decl,
                    enclosing_location=enclosing_location,
                    block_end=block_end,
                    replace_with=by_replace_with  # Replace with "assert ...;"
                ))


                # Add primary LineInfo (full removal option)
            new_line_info = LineInfo(
                id=0, # to be determined later
                line_num=i,
                enclosing_decl=enclosing_decl,
                enclosing_location=enclosing_location,
                block_end=block_end,
                replace_with=replace_with
            )

            if is_block_start and block_end > i:
                line_info_queue.append(new_line_info)
            else:
                line_infos.append(new_line_info)

        # pop from queue blocks that end here (start from the ones added later)
        while line_info_queue and line_info_queue[-1].block_end == i:
            queued_info = line_info_queue.pop()
            line_infos.append(queued_info)
            if verbose >= 2:
                print(f"Added queued removable block from line {queued_info.line_num+1} to line {i+1}")

    # check sequences of removable isolated lines and add at the end a new line_info
    # for the entire sequence (at least for first attempt)
    if optimize_sequence:
        i = 0
        while i < len(line_infos):
            info = line_infos[i]
            stripped = lines[info.line_num].strip()
            if (info.enclosing_location != "B" or
                info.replace_with is not None or stripped.startswith("invariant")
                or stripped.startswith("decreases")):
                i += 1
                continue
            start = info.line_num
            end = info.block_end
            j = i
            while j + 1 < len(line_infos):
                next_info = line_infos[j+1]
                if (next_info.enclosing_location == "B" and
                    next_info.replace_with is None and
                    next_info.line_num == end + 1):
                    end = next_info.block_end
                    j += 1
                else:
                    break
            if i == j:
                i += 1
                continue
            # add new LineInfo for the entire sequence
            new_line_info = LineInfo(
                id=0,
                line_num=start,
                enclosing_decl=info.enclosing_decl,
                enclosing_location=info.enclosing_location,
                block_end=end,
                replace_with=None,
                max_attempts=1  # only one attempt for the entire sequence
            )
            # insert after j
            line_infos.insert(j + 1, new_line_info)
            # advance i
            i = j + 2

    # renumber line_info ids
    for new_id, info in enumerate(line_infos):
        info.id = new_id

    # Check for negative tests
    contains_negative_tests = any("@invalid" in line for line in lines)

    deps_spec = {}
    deps_body = {}
    decl_kind = {}

    # count references between declarations
    for decl in declarations.values():
        decl_kind[decl.name] = decl.kind

        spec_text = "\n".join(lines[decl.header_start:decl.body_start]) if decl.body_start > decl.header_start else lines[decl.header_start]
        body_text = "\n".join(lines[decl.body_start:decl.end_line+1]) if decl.body_start >= 0 else ""


        for other_decl in declarations.keys():
            if other_decl == decl.name:
                continue

            pattern = rf'\b{other_decl}\s*\('

            c_spec = len(re.findall(pattern, spec_text))
            if c_spec > 0:
                deps_spec[(decl.name, other_decl)] = deps_spec.get((decl.name, other_decl), 0) + c_spec

            c_body = len(re.findall(pattern, body_text))
            if c_body > 0:
                deps_body[(decl.name, other_decl)] = deps_body.get((decl.name, other_decl), 0) + c_body

            declarations[other_decl].ref_count += c_spec + c_body

    # compute closure (indirect edges will have 0 counters)
    dependencies = transitive_closure_dependencies_typed(deps_spec, deps_body, decl_kind)

    # Initially all removable candidates need rechecking
    removable_decls = set()
    for info in line_infos:
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

    return FileStructure(
        lines=lines,
        line_info=line_infos,
        declarations=declarations,
        contains_negative_tests=contains_negative_tests,
        dependencies=dependencies,
        removable_decls=removable_decls
    )



# ==============================================================================
# Incremental Update After Removal
# ==============================================================================


def update_after_removal(fs: FileStructure,
                         enclosing_decl: DeclarationInfo,
                         enclosing_location: str,
                         timestamp: int,
                         removed_segments: list[tuple[int, int, str]],
                         removed_code: str,
                         new_lines: list[str]) -> None:
    """
    Incrementally update the FileStructure after successfully removing lines.

    This function maintains the FileStructure in a consistent state without
    requiring a full re-parse. It updates:
    - Line numbers in all LineInfo and DeclarationInfo objects
    - Dependency counts (decremented for removed calls)
    - Timestamps for affected declarations and their neighbors
    - The set of declarations eligible for full removal

    Args:
        fs: The file structure to update (modified in place).
        enclosing_decl: Declaration containing the removed code (or None if global).
        enclosing_location: "H" (header), "S" (spec), or "B" (body).
        timestamp: Current logical timestamp for change tracking.
        removed_segments: List of (start, end, replacement) tuples that were removed.
        removed_code: The actual source code that was removed.
        new_lines: The new list of lines after removal.
    """
    # identify (semi)'silent' removals, without impact
    silent_removal = False
    postcond_removal = False
    if (len(removed_segments) == 1 
        and removed_segments[0][0] == removed_segments[0][1]):
        line = fs.lines[removed_segments[0][0]].strip()
        if  line.startswith("decreases") or line.startswith("reads"):
            silent_removal = True
        elif line.startswith("ensures"):
            postcond_removal = True

    # update timestamp in enclosing declaration on success
    if enclosing_decl is not None and not silent_removal:
        if enclosing_location == "H":
            enclosing_decl.timestamp_body = timestamp
            enclosing_decl.timestamp_spec = timestamp
            # also delete from removable_decls since header changed
            fs.removable_decls.remove(enclosing_decl.name)
        elif enclosing_location == "S":
            enclosing_decl.timestamp_spec = timestamp
        elif enclosing_location == "B":
            enclosing_decl.timestamp_body = timestamp

    # Update line_info list - ensure positions match between line_info and lines
    new_line_info = []
    for _, info in enumerate(fs.line_info):
        # adjust line numbers
        new_start, new_end, new_replace_with = update_segment_after_removals(info.line_num, info.block_end, info.replace_with, removed_segments)
        if new_start > new_end:
            continue
        # append adjusted info
        new_info = LineInfo(
            id=info.id,
            line_num=new_start,
            enclosing_location=info.enclosing_location,
            enclosing_decl=info.enclosing_decl,
            block_end=new_end,
            replace_with=new_replace_with,
            timestamp_last_attempt=info.timestamp_last_attempt,
            num_attempts=info.num_attempts,
            max_attempts=info.max_attempts,
            num_batch_attempts=info.num_batch_attempts
        )
        new_line_info.append(new_info)

    # Update declarations dictionary
    for decl in fs.declarations.values():
        new_header_start, new_body_end, ins = update_segment_after_removals(decl.header_start, decl.end_line, None, removed_segments)
        new_body_start, new_body_end, ins = update_segment_after_removals(decl.body_start, decl.end_line, None, removed_segments)
        if new_header_start > new_body_end:
            decl.header_start = -1
            decl.body_start = -1
            decl.end_line = -1
        else:
            decl.header_start = new_header_start
            decl.body_start = new_body_start
            decl.end_line = new_body_end

    # update reference counters and neighbours_timestamp in dependencies
    if enclosing_decl is not None:
        for other_decl in fs.declarations.keys():
            if other_decl == enclosing_decl.name or other_decl not in removed_code:
                continue
            # Check if it is actually a call with parenthesis
            pattern = rf'\b{other_decl}\s*\('
            count = len(re.findall(pattern, removed_code))
            if count == 0:
                continue
            key = (enclosing_decl.name, other_decl)
            fs.dependencies[key] = fs.dependencies.get(key, 0) - count
            if verbose >= 2:
                print(f"Decrementing dependency: {key} by {count}, new count: {fs.dependencies[key]}")
                log_file.write(f"Decrementing dependency: {key} by {count}, new count: {fs.dependencies[key]}\n")
            decl_info = fs.declarations.get(other_decl)
            decl_info.ref_count = max(0, decl_info.ref_count - count   )
            if decl_info.ref_count == 0:
                fs.removable_decls.add(other_decl)
                if verbose >= 1:
                    print(f"{other_decl}: Marked for full removal due to 0 dependencies")
                    log_file.write(f"{other_decl}: Marked for full removal due to 0 dependencies\n")

        # update timestamps for neighbours
        if not silent_removal:
            for (a, b), _cnt in fs.dependencies.items():
                if a == enclosing_decl.name:
                    b_info = fs.declarations.get(b)
                    b_info.timestamp_spec_neighbors = timestamp # to recheck spec
                if b == enclosing_decl.name and enclosing_location == "S" and not postcond_removal:
                    a_info = fs.declarations.get(a)
                    a_info.timestamp_spec_neighbors = timestamp
                    a_info.timestamp_body_neighbors = timestamp

    # remove declaration if fully removed
    if enclosing_location == "H":
        fs.declarations.pop(enclosing_decl.name, None)
        for (a, b), _cnt in list(fs.dependencies.items()):
            if a == enclosing_decl.name or b == enclosing_decl.name:
                fs.dependencies.pop((a, b), None)

    # update lines and line_info in fs
    fs.lines = new_lines
    fs.line_info = new_line_info



# ==============================================================================
# Segment Manipulation Utilities (start_line, end_line, replacement)
# ==============================================================================


def add_removal_segment(segments: list[tuple[int, int, str]], new_seg: tuple[int, int, str]) -> list[tuple[int, int, str]]:
    """
    Add a segment to an ordered list of non-overlapping removal segments.

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
        ins = segments[pos][2]
    pos_end = pos+1
    while pos_end < len(segments) and segments[pos_end][0] <= end-1:
        end = max(end, segments[pos_end][1])
        pos_end += 1
    # merge segments
    segments[pos:pos_end] = [(start, end, ins)]
    return segments

def update_segment_after_removals(i: int, j: int, old_ins: str, segments: list[tuple[int, int, str]]) -> tuple[int, int, str]:
    """
    Compute new line numbers for a segment after applying removals.

    Args:
        i: Original start line of the segment.
        j: Original end line of the segment.
        old_ins: Original replacement text for this segment.
        segments: List of removed segments (start, end, replacement).

    Returns:
        Tuple of (new_start, new_end, replacement). If new_start > new_end,
        the segment was fully removed.
    """
    shift_i = 0
    shift_j = 0
    for (a, b, ins) in segments:
        if j < a:
            break
        elif i > b:
            shift_i += (b - a + 1)
            shift_j += (b - a + 1)
            if ins is not None:
                shift_i -= 1
                shift_j -= 1
        elif i >= a and j <= b: # fully removed
            if a == i and ins is not None:
                return i-shift_i, j-shift_j, ins # replaced with ins
            else:
                return i-shift_i, i-shift_i-1, None  # fully removed
        elif i >= a:
            i = b + 1 # move i past removed segment
            shift_i += (b - a + 1)
            shift_j += (b - a + 1)
            if ins is not None:
                shift_i -= 1
                shift_j -= 1
        elif j <= b:
            j = a - 1 # move j before removed segment
            break
        else: # removed in the middle, only j will be shifted
            shift_j += (b - a + 1)
            if ins is not None:
                shift_j -= 1

    return i-shift_i, j-shift_j, old_ins


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


def worth_try_removal(fs: FileStructure, info: LineInfo, timestamp: int, batch: bool, round_num: int = 1) -> bool:
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
    _ = round_num  # Reserved for future use
    enclosing_decl = info.enclosing_decl
    enclosing_location = info.enclosing_location
    last = info.timestamp_last_attempt

    if info.max_attempts != -1 and info.num_attempts >= info.max_attempts:
        recheck = False
    elif batch and info.num_batch_attempts >= max_batch_attempts:
        recheck = False
    elif enclosing_decl is None:
        recheck = last < timestamp
    elif info.enclosing_location  == "H":
        recheck = (enclosing_decl.ref_count <= 0) and (last < timestamp)
    elif enclosing_location == "B":
        ts = max(enclosing_decl.timestamp_body, enclosing_decl.timestamp_spec)
        ts = max(ts, enclosing_decl.timestamp_body_neighbors)
        recheck = last < ts
    elif enclosing_location == "S":
        ts = max(enclosing_decl.timestamp_body, enclosing_decl.timestamp_spec)
        ts = max(ts, enclosing_decl.timestamp_spec_neighbors)
        recheck = last < ts

    if verbose >= 2 and not recheck:
        start_index = info.line_num
        end_index = info.block_end if info.block_end >= start_index else start_index
        remove_segment = "\n".join(fs.lines[start_index:end_index+1])
        print(f"{enclosing_decl}: skipped: {remove_segment}")
        log_file.write(f"{enclosing_decl}: skipped: {remove_segment}\n")

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
    
    for (i, j, ins) in segments:
        new_lines.extend(lines[current:i])
        if ins is not None:
            new_lines.append(ins)
        removed_parts.append("\n".join(lines[i:j+1]))
        current = j + 1
    
    new_lines.extend(lines[current:])
    removed_code = "\n".join(removed_parts) + "\n" if removed_parts else ""
    return new_lines, removed_code


def check_removal(fs: FileStructure, info_idxs: list[int], verification_cache: dict,
                  timestamp: int, round_num: int) -> tuple[int, list[tuple[int, int, str]], str, list[str]]:
    """
    Attempt to remove one or more candidates and verify the result.

    This is the core function that:
    1. Computes the segments to remove from the candidate indices
    2. Generates the modified file content
    3. Verifies the modified file using Dafny
    4. Returns success/failure with the removal details

    Args:
        fs: Current file structure.
        info_idxs: Indices into fs.line_info of candidates to remove together.
        verification_cache: Cache mapping content hash to verification result.
        timestamp: Current logical timestamp.
        round_num: Current simplification round (affects timeout).

    Returns:
        Tuple of (removed_count, segments, removed_code, new_lines) where:
        - removed_count: Number of lines removed (0 if verification failed)
        - segments: List of (start, end, replacement) that were removed
        - removed_code: The actual code that was removed
        - new_lines: The new file lines after removal
    """
    # determine list of removal segments (i, j)
    removal_segments = [(fs.line_info[idx].line_num, fs.line_info[idx].block_end, fs.line_info[idx].replace_with) for idx in info_idxs]

    # normalize removal segments
    removal_segments = normalize_removal_segments(removal_segments)

    # determine new lines and removed code
    new_lines, removal_code = apply_removal_segments(fs.lines, removal_segments)

    # get enclosing declaration from first info (should be the same for all)
    enclosing_decl = fs.line_info[info_idxs[0]].enclosing_decl
    enclosing_location = fs.line_info[info_idxs[0]].enclosing_location

    # count lines removed, comparing new_lines with fs.lines
    removal_count = len(fs.lines) - len(new_lines)

    # marke new attempt and check if need verification
    need_verify = False
    for info_idx in info_idxs:
        info = fs.line_info[info_idx]
        info.num_attempts += 1
        if not (info.line_num == info.block_end and fs.lines[info.line_num].strip().startswith("//")):
            need_verify = True

    # in case of a batch, do not update timestamp of last attempt (to enable individual retries)
    if len(info_idxs) == 1:
        info = fs.line_info[info_idxs[0]]
        info.timestamp_last_attempt = timestamp
    else: # mark as batch attempt counter
        for info_idx in info_idxs:
            info = fs.line_info[info_idx]
            info.num_batch_attempts += 1

    # Check if the simplified file passes verification
    # (Skip verification for comment-only removals)
    if need_verify:
        contents="\n".join(new_lines)
        filter_lines = None
        filter_symbol = None
        if use_filter_symbol and enclosing_decl is not None:
            if enclosing_decl.kind == "M" and enclosing_location == "B":
                #filter_lines = (enclosing_decl.header_start + 1, enclosing_decl.end_line + 1)
                filter_symbol = enclosing_decl.name
        # Check cache
        key = sha1(contents.encode("utf-8")).hexdigest()
        if verification_cache is not None and key in verification_cache:
            cached = True
            success = verification_cache[key]  # cached result
            duration = 0.0

            # Record profiling stats for cached verification
            if enable_profiling:
                profile_stats.add_verification(duration, success, cached=True, location=enclosing_location)
        else:
            cached = False
            # Don't need to handle negative tests if changes are within the body of a method
            # that is not a text test (with 'test' or 'Test' in its name)
            if (not fs.contains_negative_tests or
                (enclosing_location == "B" and enclosing_decl.kind == "M" and
                    "test" not in enclosing_decl.name.lower())
                or enclosing_location == "H"):
                handle_neg_tests = False
            else:
                handle_neg_tests = True

            # if marked for removal, can retry with longer timeout
            timeout = verifier_timeout + round_num - 1
            if enclosing_decl is not None and enclosing_location == "H":
                timeout = timeout *2
            timeout = min(timeout, max_verifier_timeout)

            # Verify the simplified file (returns success code and duration)
            success, duration = verify_dafny_file(contents,
                                        new_lines,
                                        handle_negative_tests=handle_neg_tests,
                                        filter_symbol=filter_symbol,
                                        filter_lines=filter_lines,
                                        timeout=timeout)

            # Record profiling stats
            if enable_profiling:
                profile_stats.add_verification(duration, success, cached=False, location=enclosing_location)

            # Log timing for slow verifications
            if verbose >= 2 or (verbose >= 1 and duration > 5.0):
                print(f"  Verification took {duration:.1f}s")
                log_file.write(f"  Verification took {duration:.1f}s\n")

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
        if verbose >= 1:
            if cached:
                print(f"{name}({enclosing_location}): kept (using cache): {removal_code}")
                log_file.write(f"{name}({enclosing_location}): kept (using cache): {removal_code}\n")
            else:
                print(f"{name}({enclosing_location}): kept: {removal_code} ")
                log_file.write(f"{name}({enclosing_location}): kept: {removal_code} \n")
        return 0, removal_segments, removal_code, new_lines

    else:
        if verbose >= 1:
            print(f"{name}({enclosing_location}): removed: {removal_code} ")
            log_file.write(f"{name}({enclosing_location}): removed: {removal_code}\n")

        return removal_count, removal_segments, removal_code, new_lines


def find_removable_declaration_info(fs: FileStructure, timestamp: int) -> int:
    """
    Find a declaration that can be fully removed (no remaining references).

    Prioritizes removing entire declarations when they become unreferenced,
    as this is more efficient than removing their contents line by line.

    Args:
        fs: Current file structure.
        timestamp: Current logical timestamp.

    Returns:
        Index into fs.line_info of the declaration's header, or -1 if none found.
    """
    if fs.removable_decls is not None:
        for decl_name in fs.removable_decls:
            decl_info = fs.declarations[decl_name]
            for idx, line_info in enumerate(fs.line_info):
                if line_info.enclosing_decl == decl_info and line_info.enclosing_location == "H":
                    if line_info.timestamp_last_attempt < timestamp:
                        return idx
                    else:
                        break
    return -1


# ==============================================================================
# Main Simplification Functions
# ==============================================================================


def simplify_file(original_file: str, modified_file: str, simplified_file: str,
             start_from_simplified_file: bool = False) -> int:
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

    Returns:
        Total number of lines removed across all rounds.
    """
    # Reset profiling stats for this file
    if enable_profiling:
        global profile_stats
        profile_stats = ProfileStats()

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
            print(f"Could not find simplified file {simplified_file} to start from.")
            log_file.write(f"Could not find simplified file {simplified_file} to start from.\n")
            return 0

    # Preprocess the file structure ONCE (this analyzes everything upfront)
    original_lines = original_content.splitlines()
    modified_lines = modified_content.splitlines()

    if enable_profiling:
        preprocess_start = time.time()
    file_structure = preprocess_file(modified_lines, original_lines)
    if enable_profiling:
        profile_stats.preprocessing_time = time.time() - preprocess_start
        if verbose >= 1:
            print(f"  Preprocessing took {profile_stats.preprocessing_time:.2f}s")
            log_file.write(f"  Preprocessing took {profile_stats.preprocessing_time:.2f}s\n")

    # Print declarations found
    if verbose >= 2:
        print(f"  Preprocessed: {len(file_structure.declarations)} declarations found")
        log_file.write(f"  Preprocessed: {len(file_structure.declarations)} declarations found\n")
        for _, decl in file_structure.declarations.items():
            print(f"    - {decl.name}: header={decl.header_start+1}, body={decl.body_start+1}, end={decl.end_line+1}, timestamp_spec={decl.timestamp_spec}, timestamp_body={decl.timestamp_body}, ref_count={decl.ref_count}")
            log_file.write(f"    - {decl.name}: header={decl.header_start+1}, body={decl.body_start+1}, end={decl.end_line+1}, timestamp_spec={decl.timestamp_spec}, timestamp_body={decl.timestamp_body}, ref_count={decl.ref_count}\n")

    # Print dependencies found
    if verbose >= 2:
        print("  Declaration dependencies:")
        log_file.write("  Declaration dependencies:\n")
        for (dependent, dependee), count in file_structure.dependencies.items():
            print(f"    - {dependent} depends on {dependee}: {count} times")
            log_file.write(f"    - {dependent} depends on {dependee}: {count} times\n")

    # Print line_infos found
    if verbose >= 2:
        print(f"  Preprocessed: {len(file_structure.line_info)} removable line infos found")
        log_file.write(f"  Preprocessed: {len(file_structure.line_info)} removable line infos found\n")
        for info in file_structure.line_info:
            start = info.line_num + 1
            end = info.block_end + 1
            loc = info.enclosing_location
            decl_name = info.enclosing_decl.name if info.enclosing_decl is not None else "Global"
            print(f"    - id {info.id} lines {start}-{end}, location={loc}, decl={decl_name}")
            log_file.write(f"    - id {info.id} lines {start}-{end}, location={loc}, decl={decl_name}\n")

    # Inicialize counters, cache, timestamp
    total_removed_count = 0
    round_num = 1
    verification_cache = {}  # map from sha1 of file contents to verification result
    timestamp = 1

    # Main simplification loop - multiple rounds until no more removals
    while True:
        if verbose >= 1:
            print(f"\n========== Round {round_num} ==========")
            log_file.write(f"\n========== Round {round_num} ==========\n")

        # Count of removals this round
        round_removed_count = 0

        # Iterate through lines using preprocessed info, backwards
        resume_at_info_id_after_removal = None
        k = len(file_structure.line_info)
        while k > 0 and k <= len(file_structure.line_info):
            # determine next k, giving priority to declarations to remove
            k -= 1

            # possible jump to next removable declaration
            rmv_k = find_removable_declaration_info(file_structure, timestamp)
            if rmv_k >= 0:
                # remember position after removal to resume
                if resume_at_info_id_after_removal is None:
                    resume_at_info_id_after_removal =  file_structure.line_info[k].id
                # jump to declaration removal
                k = rmv_k
            # possible resume after previous removal
            elif resume_at_info_id_after_removal is not None:
                for idx, line_info in enumerate(file_structure.line_info):
                    if line_info.id >= resume_at_info_id_after_removal:
                        k = idx
                        if verbose >= 2:
                            print(f"Resuming at line info with id {line_info.id} after previous removal")
                            log_file.write(f"Resuming at line info with id {line_info.id} after previous removal\n")
                        break
                resume_at_info_id_after_removal = None

            # get line info
            info = file_structure.line_info[k]
            id = info.id
            recheck = worth_try_removal(file_structure, info, timestamp, False, round_num)
            if not recheck:
                continue
            enclosing_decl = info.enclosing_decl
            enclosing_location = info.enclosing_location
            line_num = info.line_num
            batch_list = [k]

            # possibly try several at once
            start = info.line_num
            stop = info.block_end
            if max_batch_size > 1 and info.enclosing_location == "B" and info.num_batch_attempts < max_batch_attempts and stop - start + 1 < max_batch_lines:
                idx = k-1
                while idx >= 0 and len(batch_list) < max_batch_size:
                    info2 = file_structure.line_info[idx]
                    if info2.enclosing_location != info.enclosing_location or info2.enclosing_decl != info.enclosing_decl:
                        break
                    start = min(info2.line_num, start)
                    stop = max(info2.block_end, stop)
                    if stop - start + 1 > max_batch_lines:
                        break
                    recheck = worth_try_removal(file_structure, info2, timestamp, True, round_num)
                    if recheck:
                        # add to batch_list
                        batch_list.append(idx)
                    idx -= 1


            # Check if removal can be done (successful verification)
            removed_count, removed_segments, removed_code, new_lines = check_removal(file_structure, batch_list, verification_cache, timestamp, round_num)
            if removed_count == 0:
                if len(batch_list) > 1:
                    k += 1 # retry individually
                continue  # could not remove

            # Increment timestamp
            timestamp += 1

            # Update file structure
            update_after_removal(file_structure, enclosing_decl, enclosing_location, timestamp, removed_segments, removed_code, new_lines)

            # Update counters
            round_removed_count += removed_count

            # May cause removal of previous line_infos (shifting others), so adjust k accordingly
            if k > len(file_structure.line_info):
                k = len(file_structure.line_info)
            while k > 0 and file_structure.line_info[k-1].id >= id:
                k -= 1

        # End of round - check if we made progress
        if round_removed_count == 0:
            if verbose >= 1:
                print(f"Round {round_num}: No more simplifications possible.")
                log_file.write(f"Round {round_num}: No more simplifications possible.\n")
            break
        else:
            if verbose >= 1:
                print(f"Round {round_num}: Removed {round_removed_count} lines.")
                log_file.write(f"Round {round_num}: Removed {round_removed_count} lines.\n")
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
        return 0

    # Save the final simplified content
    with open(simplified_file, 'w', encoding='utf-8') as file:
        file.write("\n".join(file_structure.lines))

    if verbose >= 1:
        print(f"\n========== COMPLETE ==========")
        print(f"Total rounds: {round_num}")
        print(f"Total lines removed: {total_removed_count}")
        log_file.write(f"\n========== COMPLETE ==========\n")
        log_file.write(f"Total rounds: {round_num}\n")
        log_file.write(f"Total lines removed: {total_removed_count}\n")

    # Print profiling summary
    if enable_profiling and verbose >= 1:
        profile_stats.print_summary()

    return total_removed_count


def simplify_folder(folder_with_stripped_files: str, folder_with_modified_files: str,
                    folder_with_simplified_files: str,
                    start_from_simplified_files: bool = False) -> tuple[int, int]:
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

    Returns:
        Tuple of (files_simplified, total_lines_removed).
    """
    total_simplified_files = 0
    total_removed_lines = 0
    total_time_seconds = 0

    for filename in os.listdir(folder_with_modified_files):
        if not filename.endswith('_llm.dfy'):
            continue

        match = re.match(r'^(.*)_\d+_llm\.dfy$', filename)
        if not match:
            print(f"Could not find stripped file for {filename}")
            log_file.write(f"Could not find stripped file for {filename}\n")
            continue

        base_name = match.group(1)
        stripped_filename = f"{base_name}_stripped.dfy"

        filepath_modified = os.path.join(folder_with_modified_files, filename)
        filepath_stripped = os.path.join(folder_with_stripped_files, stripped_filename)
        filepath_simplified = os.path.join(folder_with_simplified_files,
                                           filename.replace('_llm.dfy', '_llm_simplified.dfy'))

        print(f"\n{'='*60}")
        print(f"Simplifying {filename}")
        print(f"{'='*60}")
        log_file.write(f"\n{'='*60}\n")
        log_file.write(f"Simplifying {filename}\n")
        log_file.write(f"{'='*60}\n")

        # get timestamp
        timestamp_start = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())

        # simplify() now handles all rounds internally (single preprocessing)
        removed_lines_count = simplify_file(
            filepath_stripped,
            filepath_modified,
            filepath_simplified,
            start_from_simplified_file=start_from_simplified_files
        )

        timestamp_end = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
        elapsed_seconds = (
            time.mktime(time.strptime(timestamp_end, "%Y-%m-%d %H:%M:%S"))
            - time.mktime(time.strptime(timestamp_start, "%Y-%m-%d %H:%M:%S"))
        )
        total_time_seconds += elapsed_seconds

        if removed_lines_count > 0:
            print(f"\n{filename}: Simplified by removing {removed_lines_count} lines (time: {elapsed_seconds:.0f} seconds) ")
            log_file.write(f"\n{filename}: Simplified by removing {removed_lines_count} lines (time: {elapsed_seconds:.0f} seconds) \n")
            total_simplified_files += 1
            total_removed_lines += removed_lines_count
        else:
            print(f"\n{filename}: Could not be simplified (time: {elapsed_seconds:.0f} seconds)")
            log_file.write(f"\n{filename}: Could not be simplified (time: {elapsed_seconds:.0f} seconds)\n")


    print(f"\n{'='*60}")
    print(f"BATCH COMPLETE")
    print(f"Total simplified files: {total_simplified_files}")
    print(f"Total removed lines: {total_removed_lines}")
    print(f"Total time: {total_time_seconds/60:.0f} minutes")
    print(f"{'='*60}")
    log_file.write(f"\n{'='*60}\n")
    log_file.write(f"BATCH COMPLETE\n")
    log_file.write(f"Total simplified files: {total_simplified_files}\n")
    log_file.write(f"Total removed lines: {total_removed_lines}\n")
    log_file.write(f"Total time: {total_time_seconds/60:.0f} minutes\n")
    log_file.write(f"{'='*60}\n")
    return total_simplified_files, total_removed_lines


# Main entry point
if __name__ == "__main__":
    simplify_folder(r"TODO",r"TODO",r"TODO")
