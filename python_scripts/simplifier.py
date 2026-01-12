"""
Dafny Simplifier
"""

#### Parameters ####

# Path to the Dafny executable 
dafny_executable = r"TODO"

# Verbosity level (0: no output, 1: some output, 2: detailed output)
verbose = 1

# verifier timeout in seconds
verifier_timeout = 10  # Reduced from 30 to 10 for faster failure detection

# handle negative tests (tests expected to fail verification, marked with //@invalid)
handle_negative_tests = True

# EXPERIMENTAL: Use --filter-symbol for local edits (faster but may cause false negatives)
# Set to True to enable smart filtering, False for full verification (more accurate)
use_smart_filter = True

#####  Imports ##### 
import os
import subprocess
import re


#### Preprocessing and file structure analysis ####

from dataclasses import dataclass
from typing import Optional

from pyparsing import line

@dataclass
class LineInfo:
    """Preprocessed information about a single line."""
    line_num: int                    # Line number (0-indexed)
    content: str                     # Original content
    stripped: str                    # Whitespace-stripped content
    normalized: str                  # Normalized for comparison (no spaces, no fuel attributes)
    original_line_match: int         # Index of matching line in original (-1 if not found)
    enclosing_method: Optional[str]  # Name of enclosing method/lemma (None if top-level)
    enclosing_function: Optional[str]  # Name of enclosing function/predicate (None if not inside one)
    block_end: int                   # End line of block starting here (-1 if not a block start)
    replace_with: Optional[str]      # What to replace with when removing block (None if nothing)
    is_trivial: bool                 # True if line should be skipped (empty, just braces)
    is_removable: bool               # True if line could potentially be removed
    brace_depth: int                 # Cumulative brace depth at this line (after processing)


@dataclass  
class FileStructure:
    """Preprocessed structure of a Dafny file."""
    lines: list[str]                 # Original lines
    line_info: list[LineInfo]        # Preprocessed info for each line
    declarations: dict[str, tuple[int, int, int]]  # name -> (header_start, body_start, end_line)
    contains_negative_tests: bool


def count_braces_in_line(line: str) -> tuple[int, int]:
    """
    Count opening and closing braces in a line, excluding special patterns.
    Returns (open_count, close_count).
    """
    # Remove patterns that contain braces but shouldn't count
    cleaned = line
    
    # Remove multiset{...} patterns
    cleaned = re.sub(r'multiset\{[^}]*\}', '', cleaned)
    
    # Remove {:attribute ...} patterns (like {:fuel ...}, {:induction ...})
    cleaned = re.sub(r'\{:[^}]+\}', '', cleaned)
    
    # Remove set{...} patterns  
    cleaned = re.sub(r'set\{[^}]*\}', '', cleaned)
    
    # Remove string literals that might contain braces (not very robust, but works for simple cases)
    cleaned = re.sub(r'"([^"\\]|\\.)*"', '', cleaned)
    cleaned = re.sub(r"'([^'\\]|\\.)*'", '', cleaned)
    
    return cleaned.count('{'), cleaned.count('}')


def normalize_line(line: str) -> str:
    """Normalize a line for comparison: remove whitespace and {:...} attributes."""
    normalized = re.sub(r'\{\:[^}]*\}\s*', '', line)
    normalized = re.sub(r'\s+', '', normalized)
    return normalized


def compute_lcs_matching(modified_normalized: list[str], original_normalized: list[str]) -> list[int]:
    """
    Compute the Longest Common Subsequence (LCS) alignment between modified and original lines.
    
    Uses dynamic programming (like diff) to find the optimal matching.
    All original lines should be present in modified file (possibly with modifications),
    so we find which modified lines correspond to which original lines.
    
    Args:
        modified_normalized: List of normalized lines from the modified file
        original_normalized: List of normalized lines from the original file
    
    Returns:
        List where result[i] is the index in original_normalized that modified line i matches,
        or -1 if it doesn't match any original line.
    """
    m = len(modified_normalized)
    n = len(original_normalized)
    
    if n == 0:
        return [-1] * m
    
    # Build LCS table using dynamic programming
    # dp[i][j] = length of LCS of modified[0:i] and original[0:j]
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if modified_normalized[i - 1] == original_normalized[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
    
    # Backtrack to find the actual matching
    # result[i] = index in original that modified line i matches, or -1
    result = [-1] * m
    
    i, j = m, n
    while i > 0 and j > 0:
        if modified_normalized[i - 1] == original_normalized[j - 1]:
            # This is a match in the LCS
            result[i - 1] = j - 1
            i -= 1
            j -= 1
        elif dp[i - 1][j] >= dp[i][j - 1]:
            # Move up - this modified line is not part of LCS
            i -= 1
        else:
            # Move left - this original line was not matched
            j -= 1
    
    return result


# Declaration keywords
declaration_starters = ["function", "predicate", "lemma", "method", "ghost function", 
                        "ghost predicate", "ghost lemma", "ghost method"]

# Clause keywords
clause_keywords = ["requires", "ensures", "modifies", "decreases", "reads", 
                    "invariant", "fresh"]

def preprocess_file(lines: list[str], original_lines: list[str] = None) -> FileStructure:
    """
    Preprocess a Dafny file to extract structural information.
    
    This function analyzes the file once to determine for each line:
    - Whether it matches a line in the original file
    - The enclosing method/lemma (for --filter-symbol)
    - Block boundaries for multi-line removals
    - Whether the line is trivially skippable
    
    Args:
        lines: Lines of the modified file
        original_lines: Lines of the original file (for comparison)
    
    Returns:
        FileStructure with all preprocessed information
    """
    # Normalize original lines for comparison
    original_normalized = []
    if original_lines:
        original_normalized = [normalize_line(line) for line in original_lines]
    
    method_starters = ["method", "lemma"]  # Only these for --filter-symbol
    
    # Block initiators
    block_initiators = ["calc ", "forall ", "if ", "else", "calc{", "if(", 
                       "for ", "while ", "while(", "by ", "} else"]
    
    # First pass: compute brace depths and find declarations
    brace_depths = []
    current_depth = 0
    declarations = {}
    
    # Track current declaration being parsed
    current_decl_name = None
    current_decl_header_start = -1
    current_decl_body_start = -1  # Line where the body starts (first opening brace)
    current_decl_depth = 0
    
    for i, line in enumerate(lines):
        open_count, close_count = count_braces_in_line(line)
        stripped = line.strip()
        
        # Check for declaration start
        for starter in declaration_starters:
            if stripped.startswith(starter + " ") or stripped.startswith(starter + "("):
                # Extract name - handle optional attributes like {:fuel 3} between keyword and name
                # Pattern: ghost? keyword (attributes)* name
                match = re.match(rf'^(?:ghost\s+)?{starter}\s+(?:\{{:[^}}]+\}}\s*)*([A-Za-z_][A-Za-z0-9_]*)', stripped)
                if match and current_decl_name is None:
                    current_decl_name = match.group(1)
                    current_decl_header_start = i
                    current_decl_body_start = -1  # Will be set when we see the first {
                    current_decl_depth = current_depth
                break
        
        # Track body start (first opening brace after declaration header)
        if current_decl_name is not None and current_decl_body_start == -1 and open_count > 0:
            # exclude lines with ensures, requires, modifies, reads, decreases
            if not any(stripped.startswith(clause) for clause in clause_keywords):
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
                if not any(stripped.startswith(clause) for clause in clause_keywords):
                    # Declaration body ended - store header_start, body_start, end
                    body_start = current_decl_body_start
                    declarations[current_decl_name] = (current_decl_header_start, body_start, i)
                    current_decl_name = None
                    current_decl_header_start = -1
                    current_decl_body_start = -1
    
    # Second pass: build line info with all preprocessed data
    line_infos = []
    
    # Compute LCS-based matching between modified and original lines
    modified_normalized = [normalize_line(line) for line in lines]
    lcs_matching = compute_lcs_matching(modified_normalized, original_normalized)
    
    # Build a reverse lookup: header_start -> (name, body_start, end)
    decl_by_header = {header_start: (name, body_start, end) 
                      for name, (header_start, body_start, end) in declarations.items()}
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        normalized = modified_normalized[i]
        
        # Check if trivial
        is_trivial = (normalized == "" or normalized == "{" or 
                     normalized == "}" or normalized == "{}")
        
        # Get the LCS-based match for this line
        original_match = lcs_matching[i]
        
        # Find enclosing method/lemma/function/predicate (only if inside the BODY, not the header)
        enclosing_method = None
        enclosing_function = None
        for name, (header_start, body_start, end) in declarations.items():
            # Line must be INSIDE the body (between body_start and end, inclusive)
            # Lines in the header (requires/ensures/etc.) are NOT inside the method body
            if body_start <= i <= end:
                # Check if it's a method or lemma (for --filter-symbol)
                decl_line = lines[header_start].strip()
                if any(decl_line.startswith(s + " ") or decl_line.startswith(s + "(") 
                       for s in declaration_starters):
                    if any(decl_line.startswith(s + " ") or decl_line.startswith(s + "(") 
                       for s in method_starters):
                        enclosing_method = name
                    else:
                        enclosing_function = name
                    break
        
        # Determine block end and replace_with
        block_end = -1
        replace_with = None
        is_removable = not is_trivial
        
        # Track if we need to add a second LineInfo for "assert...by" statements
        add_by_replacement_option = False
        by_replace_with = None
        by_block_end = -1
        
        if not is_trivial:
            # Check if this is a declaration start (use precomputed info from first pass)
            if i in decl_by_header:
                _, _, block_end = decl_by_header[i]
            # Check if this starts a block
            elif any(stripped.startswith(token) for token in block_initiators):
                block_end, replace_with = _find_block_end(lines, i, brace_depths)
            elif stripped.startswith("assert ") and " by {" in stripped:
                # Assert with inline "by {" block - create TWO options:
                # 1. Remove entire statement (this LineInfo)
                # 2. Replace just the "by {...}" part with ";" (second LineInfo below)
                block_end, _ = _find_block_end(lines, i, brace_depths)
                
                # Prepare second option: replace "by {...}" with ";"
                add_by_replacement_option = True
                by_block_end = block_end
                # Replace the line with everything before " by {" plus ";"
                leading = re.match(r'^\s*', line).group(0)
                by_pos = stripped.find(" by {")
                by_replace_with = leading + stripped[:by_pos] + ";"
            elif (stripped.startswith("assert ") or stripped.startswith("==")) and not stripped.endswith(";") and "//" not in stripped:
                # Multi-line statement (without inline by)
                block_end = _find_statement_end(lines, i)
            elif any(stripped.startswith(clause) for clause in clause_keywords):
                # Multiline clause - find the end of the clause
                block_end = _find_clause_end(lines, i)
            elif stripped.startswith("}") and not stripped.startswith("} else"):
                # Don't remove closing braces alone
                is_removable = False
            else:
                # Single line
                block_end = i
        
        # Add primary LineInfo (full removal option)
        line_infos.append(LineInfo(
            line_num=i,
            content=line,
            stripped=stripped,
            normalized=normalized,
            original_line_match=original_match,
            enclosing_method=enclosing_method,
            enclosing_function=enclosing_function,
            block_end=block_end,
            replace_with=replace_with,
            is_trivial=is_trivial,
            is_removable=is_removable,
            brace_depth=brace_depths[i] if i < len(brace_depths) else 0
        ))
        
        # For "assert...by" statements, add a second LineInfo for "replace by with ;" option
        if add_by_replacement_option:
            line_infos.append(LineInfo(
                line_num=i,
                content=line,
                stripped=stripped,
                normalized=normalized,
                original_line_match=original_match,
                enclosing_method=enclosing_method,
                enclosing_function=enclosing_function,
                block_end=by_block_end,
                replace_with=by_replace_with,  # Replace with "assert ...;"
                is_trivial=is_trivial,
                is_removable=is_removable,
                brace_depth=brace_depths[i] if i < len(brace_depths) else 0
            ))
    
    # Check for negative tests
    contains_negative_tests = any("@invalid" in line for line in lines)
    
    return FileStructure(
        lines=lines,
        line_info=line_infos,
        declarations=declarations,
        contains_negative_tests=contains_negative_tests
    )


def _find_block_end(lines: list[str], start_index: int, brace_depths: list[int]) -> tuple[int, Optional[str]]:
    """Find the end of a block starting at start_index."""
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
                                   for token in declaration_starters):
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
    """Find the end of a statement (ends with ';' or contains '//')."""
    for i in range(start_index + 1, len(lines)):
        stripped = lines[i].strip()
        if stripped.endswith(";") or "//" in lines[i]:
            return i
    return start_index


def _find_clause_end(lines: list[str], start_index: int) -> int:
    """
    Find the end of a multiline clause (requires, ensures, invariant, etc.).
    
    A clause ends when the next line:
    - Starts with another clause keyword (requires, ensures, modifies, decreases, reads, invariant)
    - Starts with an open brace '{'
    - Is empty/whitespace only
    - Starts with a declaration keyword (function, lemma, etc.)
    """
    declaration_starters = ["function", "lemma", "predicate", "method", 
                           "ghost function", "ghost predicate", "ghost method"]
    
    for i in range(start_index + 1, len(lines)):
        stripped = lines[i].strip()
        
        # Empty line ends the clause
        if not stripped:
            return i - 1
        
        # Opening brace ends the clause
        if stripped.startswith("{"):
            return i - 1
        
        # Another clause keyword ends the current clause
        if any(stripped.startswith(kw) for kw in clause_keywords):
            return i - 1
        
        # A declaration starts (we've gone too far)
        if any(stripped.startswith(decl + " ") or stripped.startswith(decl + "(") 
               for decl in declaration_starters):
            return i - 1
    
    return start_index


def update_after_removal(file_structure: FileStructure, start_index: int, end_index: int, 
                         replace_line: str = None, original_lines: list[str] = None) -> FileStructure:
    """
    Incrementally update the preprocessed FileStructure after removing lines.
    
    The original_line_match values are preserved since they're indices into the original file
    (which doesn't change). We only need to check if a replacement line matches the original.
    
    Args:
        file_structure: The current file structure
        start_index: First line removed (0-indexed)
        end_index: Last line removed (0-indexed, inclusive)
        replace_line: Optional replacement line (e.g., "}" when removing "} else {...}")
        original_lines: Original file lines (needed to check if replacement matches)
    
    Returns:
        Updated FileStructure
    """
    removed_count = end_index - start_index + 1
    if replace_line is not None:
        removed_count -= 1  # One line is being replaced, not fully removed
    
    # Update lines list
    new_lines = file_structure.lines[:start_index]
    if replace_line is not None:
        new_lines.append(replace_line)
    new_lines.extend(file_structure.lines[end_index + 1:])
    
    # Build normalized original lines for checking replacement (if needed)
    original_normalized = []
    if original_lines and replace_line is not None:
        original_normalized = [normalize_line(line) for line in original_lines]
    
    # Update line_info list - ensure positions match between line_info and lines
    new_line_info = []
    
    # First, add entries for lines BEFORE the removal (positions 0 to start_index-1)
    for info in file_structure.line_info:
        if info.line_num < start_index:
            # Lines before removal: adjust block_end if it pointed past the removal
            # original_line_match stays the same (index into original file doesn't change)
            new_info = LineInfo(
                line_num=info.line_num,
                content=info.content,
                stripped=info.stripped,
                normalized=info.normalized,
                original_line_match=info.original_line_match,  # Unchanged
                enclosing_method=info.enclosing_method,
                enclosing_function=info.enclosing_function,
                block_end=info.block_end - removed_count if info.block_end > end_index else info.block_end,
                replace_with=info.replace_with,
                is_trivial=info.is_trivial,
                is_removable=info.is_removable,
                brace_depth=info.brace_depth
            )
            new_line_info.append(new_info)
    
    # If there's a replacement line, create a LineInfo for it at position start_index
    if replace_line is not None:
        replace_stripped = replace_line.strip()
        replace_normalized = normalize_line(replace_line)
        
        # Check if replacement line matches any line in original (simple check, not LCS)
        replace_original_match = -1
        for j, orig_norm in enumerate(original_normalized):
            if replace_normalized == orig_norm:
                replace_original_match = j
                break
        
        # Determine if trivial
        is_trivial = (replace_normalized == "" or replace_normalized == "{" or 
                     replace_normalized == "}" or replace_normalized == "{}")
        
        # Get enclosing method from the info at start_index (if it exists)
        enclosing_method = None
        enclosing_function = None
        for info in file_structure.line_info:
            if info.line_num == start_index:
                enclosing_method = info.enclosing_method
                enclosing_function = info.enclosing_function
                break
        
        replace_info = LineInfo(
            line_num=start_index,
            content=replace_line,
            stripped=replace_stripped,
            normalized=replace_normalized,
            original_line_match=replace_original_match,
            enclosing_method=enclosing_method,
            enclosing_function=enclosing_function,
            block_end=start_index,  # Single line
            replace_with=None,
            is_trivial=is_trivial,
            is_removable=not is_trivial,
            brace_depth=0  # Approximate
        )
        new_line_info.append(replace_info)
    
    # Now add entries for lines AFTER the removal (adjusted positions)
    for info in file_structure.line_info:
        # Skip removed lines
        if start_index <= info.line_num <= end_index:
            continue
        
        # Adjust indices for lines after the removal
        if info.line_num > end_index:
            new_line_num = info.line_num - removed_count
            # original_line_match stays the same (index into original file doesn't change)
            new_info = LineInfo(
                line_num=new_line_num,
                content=info.content,
                stripped=info.stripped,
                normalized=info.normalized,
                original_line_match=info.original_line_match,  # Unchanged
                enclosing_method=info.enclosing_method,  # Keep same (method still exists)
                enclosing_function=info.enclosing_function,
                block_end=info.block_end - removed_count if info.block_end > end_index else info.block_end,
                replace_with=info.replace_with,
                is_trivial=info.is_trivial,
                is_removable=info.is_removable,
                brace_depth=info.brace_depth  # May be slightly off but doesn't affect removal logic
            )
            new_line_info.append(new_info)
    
    # Update declarations dictionary
    new_declarations = {}
    for name, (header_start, body_start, end) in file_structure.declarations.items():
        # Check if this declaration was completely removed
        if start_index <= header_start and end <= end_index:
            # Entire declaration removed, skip it
            continue
        
        # Adjust indices
        new_header_start = header_start
        new_body_start = body_start
        new_end = end
        
        if header_start > end_index:
            new_header_start = header_start - removed_count
        if body_start > end_index:
            new_body_start = body_start - removed_count
        if end > end_index:
            new_end = end - removed_count
        
        new_declarations[name] = (new_header_start, new_body_start, new_end)
    
    return FileStructure(
        lines=new_lines,
        line_info=new_line_info,
        declarations=new_declarations,
        contains_negative_tests=file_structure.contains_negative_tests
    )


#### Dafny verification functions ####

def verify_dafny_file(filepath: str, handle_negative_tests: bool = handle_negative_tests, 
                      filter_symbol: str = None) -> int:
    """
    Verifies a Dafny file using the Dafny verifier.
    
    Args:
        filepath: Path to the Dafny file
        handle_negative_tests: Whether to run negative tests
        filter_symbol: Optional method/function name to filter verification (uses --filter-symbol)
    
    Returns:
        1 if verification succeeds, 0 if verification fails, -1 if syntax errors
    """
    # Build command
    cmd = [
        dafny_executable,
        "verify", 
        filepath,
        f"--verification-time-limit:{verifier_timeout}",
        "--allow-warnings:true"
    ]
    
    # Add filter-symbol if specified
    if filter_symbol:
        cmd.append(f"--filter-symbol={filter_symbol}")
        if verbose >= 2:
            print(f"  [SMART] Using --filter-symbol={filter_symbol}")

    # Run the verifier
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)     
    stdout, _ = process.communicate()

    # Remove errors regarding counter-examples
    cleaned = "\n".join(
        line for line in stdout.decode('utf-8').splitlines() 
        if not line.startswith("Prover error")
    )

    # Check for errors in output
    if b"resolution/type errors" in stdout or b"parse errors" in stdout:
        return -1  # syntax errors        
    if not cleaned.endswith(' 0 errors'): 
        return 0  # verification failed
           
    # Run negative tests if required
    if handle_negative_tests:
        # Temporary file name for negative tests
        new_filepath = filepath[:-4] + "_negative.dfy"

        # Read the Dafny code from the file
        with open(filepath, 'r') as file:
            dafny_code = file.read()
        lines = dafny_code.splitlines()

        # Iterate over the lines
        for index in range(len(lines)):
            line = lines[index]
            if not line.strip().startswith("//@invalid"):
                continue
            # Erase this string in this line and save to file
            old_line = line
            lines[index] = line.replace("//@invalid", "")                 
            with open(new_filepath, 'w') as new_file:
                new_file.writelines('\n'.join(lines))
            # Call the verifier again on the new file (no filter for negative tests)
            success = verify_dafny_file(new_filepath, False, None)
            # If passes, return failure
            if success == 1:
                return 0  # failure
            # Otherwise restore the old line and continue
            lines[index] = old_line

    return 1  # success


#### Simplification functions ####


def simplify(original_file: str, modified_file: str, simplified_file: str, 
             start_from_simplified_file: bool = False) -> int:    
    """
    Simplify a Dafny file by removing lines not present in the original file 
    and checking it still verifies.
    
    Uses preprocessing to analyze file structure ONCE upfront.
    Runs multiple rounds internally until no more removals are possible.
    """
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
            return 0

    # Split into lines
    original_lines = original_content.splitlines()
    modified_lines = modified_content.splitlines()
    
    # Preprocess the file structure ONCE (this analyzes everything upfront)
    file_structure = preprocess_file(modified_lines, original_lines)
    
    
    if verbose >= 2:
        print(f"  Preprocessed: {len(file_structure.declarations)} declarations found")
        for name, (header_start, body_start, end) in file_structure.declarations.items():
            print(f"    - {name}: header={header_start+1}, body={body_start+1}, end={end+1}")
        
        print("  LCS-based line matching:")
        for info in file_structure.line_info:
            if info.original_line_match >= 0:
                print(f"    Line {info.line_num+1}: '{info.stripped[:50]}...' -> Original line {info.original_line_match+1}")

    # Total counter for removed lines across all rounds
    total_removed_count = 0
    round_num = 1
    
    # MULTI-ROUND LOOP - continue until no more removals in a full pass
    affected_methods = None  # None means all methods; set means only these methods
    
    while True:
        if verbose >= 1:
            print(f"\n========== Round {round_num} ==========")
            if affected_methods is not None:
                print(f"  (Focusing on: {affected_methods or 'top-level'})")
        
        round_removed_count = 0
        new_affected_methods = set()  # Track which methods we modify this round
        global_removal = False
        need_new_run = False
        
        # Iterate through lines using preprocessed info, backwards
        k = len(file_structure.line_info)
        while k > 0:
            k -= 1
            info = file_structure.line_info[k]
            
            # Skip trivial lines, or lines that match original, or non-removable lines
            if info.is_trivial or  info.original_line_match >= 0 or not info.is_removable:
                continue

            # Optimization: if we're focusing on specific methods, skip others
            if affected_methods is not None and info.enclosing_method not in affected_methods:
                continue
            
            # Skip lines inside function/predicate bodies - they have no internal proof code to simplify
            if info.enclosing_function is not None:
                continue

            # Determine the block to remove
            # Note: Use info.line_num, not k, because line_info may have multiple entries per line
            start_index = info.line_num
            end_index = info.block_end if info.block_end >= start_index else start_index
            replace_with = info.replace_with
            
            # Create simplified lines without this block
            new_lines = file_structure.lines[:]
            remove_segment = "\n".join(new_lines[start_index:end_index+1])
            del new_lines[start_index:end_index+1]

            # If need to replace with something, do it
            if replace_with is not None:
                new_lines.insert(start_index, replace_with)

            # Save to simplified file 
            with open(simplified_file, 'w', encoding='utf-8') as file:
                file.write("\n".join(new_lines))

            # Get the enclosing method for --filter-symbol
            filter_symbol = info.enclosing_method if use_smart_filter else None

            # Check if the simplified file passes verification
            # (Skip verification for comment-only removals)
            if not (end_index == start_index and remove_segment.strip().startswith("//")):
                success = verify_dafny_file(simplified_file, 
                                            handle_negative_tests=file_structure.contains_negative_tests,
                                            filter_symbol=filter_symbol)
                if success != 1:
                    if verbose >= 1:
                        method_info = f" (inside {filter_symbol})" if filter_symbol else ""
                        print(f"Could not remove segment{method_info}: {remove_segment[:80]}...")
                    continue  

                if filter_symbol:
                    # Track which method was affected for next round focus
                    new_affected_methods.add(filter_symbol)
                    need_new_run = True
                elif not any(info.stripped.startswith(token + " ") or info.stripped.startswith(token + "(")
                            for token in declaration_starters):
                    global_removal = True
                    need_new_run = True
                    # declaration removal does not require next round         
                            
            # If successful, incrementally update file structure
            file_structure = update_after_removal(file_structure, start_index, end_index, replace_with, original_lines)
            
            removed_count = end_index - start_index + 1
            if replace_with is not None:
                removed_count -= 1

            if verbose >= 1:
                method_info = f" (inside {filter_symbol})" if filter_symbol else ""
                #print(f"Removed not needed segment{method_info}: {remove_segment[:80]}...")
                print(f"Removed not needed segment{method_info}: {remove_segment}")
            round_removed_count += (end_index - start_index + 1)
            

        # End of round - check if we made progress
        if round_removed_count == 0:
            if verbose >= 1:
                print(f"Round {round_num}: No more simplifications possible.")
            break

        if verbose >= 1:
            print(f"Round {round_num}: Removed {round_removed_count} lines.")
        total_removed_count += round_removed_count
        
        # Focus next round on affected methods only
        affected_methods = new_affected_methods if not global_removal else None
        
        # If only delcaration removals were made, no need for another round
        if not need_new_run:
            if verbose >= 1:
                print(f"Round {round_num}: No need for further rounds.")
            break

        round_num += 1


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

    return total_removed_count


def simplify_folder(folder_with_stripped_files: str, folder_with_modified_files: str, 
                    folder_with_simplified_files: str, start_filename: str = None, 
                    end_filename: str = None, restrict_to_set=None, 
                    start_from_simplified_files: bool = False) -> tuple[int, int]:
    """
    Tries to simplify all Dafny files in a folder with modified files ending in "_NN_llm.dfy". 
    Considers as original files files with same name but ending in "_stripped.dfy" in another folder.
    Saves the simplified files in a third folder, with names ending in "_NN_llm_simplified.dfy".
    
    Note: simplify() now handles all rounds internally with single preprocessing.
    """
    total_simplified_files = 0
    total_removed_lines = 0
    start = False if start_filename is not None else True

    for filename in os.listdir(folder_with_modified_files):
        if not filename.endswith('_llm.dfy'):
            continue
        if not start:
            if filename == start_filename:
                start = True
            else:
                continue
        if restrict_to_set is not None and filename not in restrict_to_set:
            continue
        
        match = re.match(r'^(.*)_\d+_llm\.dfy$', filename)
        if not match:
            print(f"Could not find stripped file for {filename}")
            if end_filename and filename == end_filename:
                break
            else:
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
        
        # simplify() now handles all rounds internally (single preprocessing)
        removed_lines_count = simplify(
            filepath_stripped, 
            filepath_modified, 
            filepath_simplified, 
            start_from_simplified_file=start_from_simplified_files
        )

        if removed_lines_count > 0:
            print(f"\n{filename}: Simplified by removing {removed_lines_count} lines")
            total_simplified_files += 1
            total_removed_lines += removed_lines_count
        else:
            print(f"\n{filename}: Could not be simplified")

        if end_filename and filename == end_filename:
            break

    print(f"\n{'='*60}")
    print(f"BATCH COMPLETE")
    print(f"Total simplified files: {total_simplified_files}")
    print(f"Total removed lines: {total_removed_lines}")
    print(f"{'='*60}")
    return total_simplified_files, total_removed_lines


def simplify_single_file(original_file: str, modified_file: str, output_file: str = None) -> int:
    """
    Simplify a single Dafny file.
    
    Note: simplify() now handles all rounds internally with single preprocessing.
    
    Args:
        original_file: Path to the original (stripped) file
        modified_file: Path to the modified file to simplify
        output_file: Optional output path (defaults to modified_file with _simplified suffix)
    
    Returns:
        Total number of removed lines
    """
    if output_file is None:
        output_file = modified_file[:-4] + "_simplified.dfy"
    
    # simplify() now handles all rounds internally (single preprocessing)
    total_removed = simplify(original_file, modified_file, output_file)
    
    return total_removed


# Example usage:
if __name__ == "__main__":
    # For batch processing:
    # simplify_folder(
    #     r"C:\path\to\stripped_files",
    #     r"C:\path\to\modified_files", 
    #     r"C:\path\to\output",
    #     start_from_simplified_files=True
    # )
    
    # For single file:
    # simplify_single_file(
    #     r"C:\path\to\original.dfy",
    #     r"C:\path\to\modified.dfy",
    #     r"C:\path\to\output.dfy"
    # )
    
    # Your original folder processing:
    simplify_folder(r"TODO", r"TODO", r"TODO")
