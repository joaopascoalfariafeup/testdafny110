"""
Dafny Simplifier: simplifies Dafny programs by removing lines while preserving verification.

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

# optimization features
use_filter_symbol = True # Use --filter-symbol to speed up verification when possible
optimize_sequence = True  # Try to optimize removal sequence based on dependencies

#####  Imports ##### 
from hashlib import sha1
import os
import subprocess
import re
from dataclasses import dataclass
import time
from typing import Optional
from typing import List
import tempfile
from collections import deque

#### Logging ####
log_file_path = "simplifier_log.txt"
log_file = open(log_file_path, "w", encoding="utf-8")


#### Preprocessing and file structure analysis ####
@dataclass
class LineInfo:
    """Preprocessed information about a single line."""
    line_num: int                    # Line number (0-indexed)
    content: str                     # Original content
    stripped: str                    # Whitespace-stripped content
    normalized: str                  # Normalized for comparison (no spaces, no fuel attributes)
    enclosing_method: Optional[str]  # Name of enclosing method/lemma (None if top-level)
    enclosing_function: Optional[str]  # Name of enclosing function/predicate (None if not inside one)
    enclosing_location: Optional[str]  # H-header, S-spec, B-body, None
    block_end: int                   # End line of block starting here (-1 if not a block start)
    replace_with: Optional[str]      # What to replace with when removing block (None if nothing)
    is_removable: bool               # True if line could potentially be removed
    brace_depth: int                 # Cumulative brace depth at this line (after processing)

@dataclass  
class FileStructure:
    """Preprocessed structure of a Dafny file."""
    lines: list[str]                 # Original lines
    line_info: list[LineInfo]        # Preprocessed info for each line
    declarations: dict[str, tuple[int, int, int]]  # name -> (header_start, body_start, end_line)
    contains_negative_tests: bool
    dependencies: dict[tuple[str, str], int] = None # decl A depends on decl B -> (A,B): count


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


_attr_re = re.compile(r'\{\:[^}]*\}\s*')
_space_re = re.compile(r'\s+')

def normalize_line(line: str) -> str:
    """Normalize a line for comparison: ignore // comments, remove {:...} and whitespace."""
    # Remove line comments
    line = line.split('//', 1)[0]

    # Remove Dafny attributes {: ... }
    line = _attr_re.sub('', line)

    # Remove all whitespace
    line = _space_re.sub('', line)

    return line


def compute_subsequence_matching(
    modified_normalized: List[str],
    original_normalized: List[str],
) -> List[int]:
    """
    O(m+n) subsequence matcher.
    Ignores empty normalized lines.
    Assumes original_normalized is a subsequence of modified_normalized.
    """
    mod2orig = [-1] * len(modified_normalized)

    i = 0  # modified index
    j = 0  # original index

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

    # check if remainin lines are empty
    while j < len(original_normalized):
        if original_normalized[j] != "":
            return compute_lcs_matching(modified_normalized, original_normalized)
        j += 1

    return mod2orig

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

method_starters = ["method", "lemma"]  # Only these for --filter-symbol

# Block initiators
block_initiators = ["calc ", "forall ", "if ", "else", "calc{", "if(", 
                    "for ", "while ", "while(", "by ", "} else"]

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
    lcs_matching = compute_subsequence_matching(modified_normalized, original_normalized)
    #lcs_matching = compute_lcs_matching(modified_normalized, original_normalized)
    
    # Build a reverse lookup: header_start -> (name, body_start, end)
    decl_by_header = {header_start: (name, body_start, end) 
                      for name, (header_start, body_start, end) in declarations.items()}
    

    # queue of line_info corresponding to start of blocks to be inserted later at end of block
    line_info_queue = deque()
      
    for i, line in enumerate(lines):
        stripped = line.strip()
        normalized = modified_normalized[i]
        
        # Get the LCS-based match for this line
        original_match = lcs_matching[i]

        # Check if is removable
        is_removable = not (normalized == "" or normalized == "{" or 
                           normalized == "}" or normalized == "{}") and original_match == -1  # Only removable if not matching original

        # Find enclosing method/lemma/function/predicate
        enclosing_method = None
        enclosing_function = None
        enclosing_location = None
        for name, (header_start, body_start, end) in declarations.items():
            if header_start <= i <= end:
                # Check if it's a method or lemma (for --filter-symbol)
                decl_line = lines[header_start].strip()
                if any(decl_line.startswith(s + " ") or decl_line.startswith(s + "(") 
                    for s in declaration_starters):
                    if any(decl_line.startswith(s + " ") or decl_line.startswith(s + "(") 
                    for s in method_starters):
                        enclosing_method = name
                    else:
                        enclosing_function = name
                # define location type in enclosing method/function 
                if i == header_start:
                    enclosing_location = "H"  # Header line
                elif header_start <= i < body_start:
                    enclosing_location = "S"  # Spec (requires/ensures/etc.)
                else:
                    enclosing_location = "B"  # Body
                break
        
        # Determine block end and replace_with
        block_end = -1
        replace_with = None
        
        # Track if we need to add a second LineInfo for "assert...by" statements
        add_by_replacement_option = False
        by_replace_with = None
        by_block_end = -1

        is_block_start = False
        
        # Check if this is a declaration start (use precomputed info from first pass)
        code_part = stripped.split("//")[0].rstrip()  
        if i in decl_by_header:
            _, _, block_end = decl_by_header[i]
        # Check if this starts a block
        elif any(code_part.startswith(token) for token in block_initiators):
            block_end, replace_with = _find_block_end(lines, i, brace_depths)
            is_block_start = True
        elif code_part.startswith("assert ") and " by {" in code_part:
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
        elif (code_part.startswith("assert ") or code_part.startswith("==")) and not code_part.endswith(";"):
            if code_part.startswith("assert ")  and i + 1 < len(lines) and lines[i + 1].strip().startswith("by "):
                block_end, _ = _find_block_end(lines, i, brace_depths)
            else:
                block_end = _find_statement_end(lines, i)
        elif any(code_part.startswith(clause) for clause in clause_keywords):
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
        if enclosing_function is not None and enclosing_location == "B":
            is_removable = False

        # Add primary LineInfo (full removal option)
        new_line_info = LineInfo(
            line_num=i,
            content=line,
            stripped=stripped,
            normalized=normalized,
            enclosing_method=enclosing_method,
            enclosing_function=enclosing_function,
            enclosing_location=enclosing_location,
            block_end=block_end,
            replace_with=replace_with,
            is_removable=is_removable,
            brace_depth=brace_depths[i] if i < len(brace_depths) else 0
        )

        if is_block_start and block_end > i:
            line_info_queue.append(new_line_info)
        else:
            line_infos.append(new_line_info)
        
        # For "assert...by" statements, add a second LineInfo for "replace by with ;" option
        if add_by_replacement_option:
            line_infos.append(LineInfo(
                line_num=i,
                content=line,
                stripped=stripped,
                normalized=normalized,
                enclosing_method=enclosing_method,
                enclosing_function=enclosing_function,
                enclosing_location=enclosing_location,
                block_end=by_block_end,
                replace_with=by_replace_with,  # Replace with "assert ...;"
                is_removable=is_removable,
                brace_depth=brace_depths[i] if i < len(brace_depths) else 0
            ))
    

        # pop from queue blocks that end here (start from the ones added later)
        while line_info_queue and line_info_queue[-1].block_end == i:
            queued_info = line_info_queue.pop()
            line_infos.append(queued_info)
            if queued_info.is_removable and verbose >= 2: 
                print(f"Added queued removable block from line {queued_info.line_num+1} to line {i+1}")

    # check sequences of removable isolated lines and add at the end a new line_info
    # for the entire sequence
    if optimize_sequence:
        i = 0
        while i < len(line_infos):
            info = line_infos[i]
            if (not info.is_removable or info.enclosing_location != "B" or 
                info.replace_with is not None or info.stripped.startswith("invariant")
                or info.stripped.startswith("decreases")):
                i += 1
                continue
            start = info.line_num
            end = info.block_end
            j = i 
            while j + 1 < len(line_infos):
                next_info = line_infos[j+1]
                if (next_info.is_removable and 
                    next_info.enclosing_location == "B" and 
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
                line_num=start,
                content="\n".join(lines[start:end+1]),
                stripped=lines[start].strip(),
                normalized=normalize_line(lines[start]),
                enclosing_method=info.enclosing_method,
                enclosing_function=info.enclosing_function,
                enclosing_location=info.enclosing_location,
                block_end=end,
                replace_with=None,
                is_removable=True,
                brace_depth=info.brace_depth
            )  
            # insert after j
            line_infos.insert(j + 1, new_line_info)
            # advance i
            i = j + 2

    # Check for negative tests
    contains_negative_tests = any("@invalid" in line for line in lines)
    
    # check dependencies between delcarations by scanning line_infos that represent full delcaration bodies
    for line_info in line_infos:
        enclosing_decl = line_info.enclosing_method or line_info.enclosing_function
        if enclosing_decl is not None and line_info.enclosing_location == "H":
            # get the full declaration content
            start_index = line_info.line_num
            end_index = line_info.block_end if line_info.block_end >= start_index else start_index
            decl_content = "\n".join(lines[start_index:end_index+1])
            for other_decl in declarations.keys():
                if other_decl != enclosing_decl and other_decl in decl_content:
                    # check if it is actually a call with parenthesis
                    pattern = rf'\b{other_decl}\s*\('
                    count = len(re.findall(pattern, decl_content))
                    if count > 0:
                        key = (enclosing_decl, other_decl)
                        dependencies[key] = dependencies.get(key, 0) + count

    return FileStructure(
        lines=lines,
        line_info=line_infos,
        declarations=declarations,
        contains_negative_tests=contains_negative_tests,
        dependencies=dependencies
    )


# TODO: confusion with if/else expressions
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
    """Find the end of a statement with ';'  """
    for i in range(start_index + 1, len(lines)):
        stripped = lines[i].strip()
        # ignore text after '//' when checking for ';'
        code_part = stripped.split("//")[0].rstrip()        
        if code_part.endswith(";"):
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


def update_after_removal(file_structure: FileStructure, 
                         index_of_line_info_removed: int,
                         start_index: int, end_index: int, 
                         replace_line: str = None, 
                         new_lines: list[str] = None,
                         new_dependencies: dict = None) -> FileStructure:
    """
    Incrementally update the preprocessed FileStructure after removing lines.
    
    
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
    
    
    # Update line_info list - ensure positions match between line_info and lines
    new_line_info = []
    
    # scan in order
    for i, info in enumerate(file_structure.line_info):
        if i == index_of_line_info_removed:
            if replace_line is not None:
                new_stripped = replace_line.strip()
                new_normalized = normalize_line(replace_line)
                new_info = LineInfo(
                    line_num=info.line_num,
                    content=replace_line,
                    stripped=new_stripped,
                    normalized=new_normalized,
                    enclosing_method=info.enclosing_method,
                    enclosing_function=info.enclosing_function,
                    enclosing_location=info.enclosing_location,
                    block_end=info.line_num,  # single line replacement
                    replace_with=None,
                    is_removable=info.is_removable,  # assume replacement line is not removable
                    brace_depth=info.brace_depth  # May be slightly off but doesn't affect removal logic
                )
                new_line_info.append(new_info)  
            continue
        # Skip removed lines
        if info.line_num >= start_index and info.block_end <= end_index:
            continue
        # Adjust line numbers
        if info.line_num < start_index:
            new_start = info.line_num
        elif info.line_num > end_index:
            new_start = info.line_num - removed_count
        else:
            new_start = start_index if replace_line is None else start_index + 1
        if info.block_end < start_index:
            new_end = info.block_end
        elif info.block_end > end_index:
            new_end = info.block_end - removed_count
        else:
            new_end = start_index-1 if replace_line is None else start_index
        # append adjusted info
        new_info = LineInfo(
            line_num=new_start,
            content=info.content,
            stripped=info.stripped,
            normalized=info.normalized,
            enclosing_method=info.enclosing_method,
            enclosing_function=info.enclosing_function,
            enclosing_location=info.enclosing_location,
            block_end=new_end,
            replace_with=info.replace_with,
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
        contains_negative_tests=file_structure.contains_negative_tests,
        dependencies=new_dependencies if new_dependencies is not None else file_structure.dependencies
    )


#### Dafny verification functions ####

# For temporary files with Dafny programs to be verified
temp_dafny_path = os.path.join(tempfile.gettempdir(), "dafny_temp_file.dfy")


def verify_dafny_file(contents: str, handle_negative_tests: bool = handle_negative_tests, 
                      filter_symbol: str = None, timeout: int = verifier_timeout) -> int:
    """
    Verifies a Dafny file using the Dafny verifier.
    
    Args:
        contents: The contents of the Dafny file
        handle_negative_tests: Whether to run negative tests
        filter_symbol: Optional method/function name to filter verification (uses --filter-symbol)
    
    Returns:
        1 if verification succeeds, 0 if verification fails, -1 if syntax errors
    """

    # Save to temporary file 
    with open(temp_dafny_path, 'w', encoding='utf-8') as file:
        file.write(contents)

    # Build command
    cmd = [
        dafny_executable,
        "verify", 
        temp_dafny_path,
        f"--verification-time-limit:{timeout}",
        "--allow-warnings:true"
    ]
    if filter_symbol:
        cmd.append(f"--filter-symbol={filter_symbol}")

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
        lines = contents.splitlines()
        for index in range(len(lines)):
            line = lines[index]
            if not line.strip().startswith("//@invalid"):
                continue
            # Erase this string in this line 
            old_line = line
            lines[index] = line.replace("//@invalid", "") 
            new_content = "\n".join(lines)                
            # Call the verifier again on the new file (no filter for negative tests)
            success = verify_dafny_file(new_content, False, None)
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
            log_file.write(f"Could not find simplified file {simplified_file} to start from.\n")
            return 0

    # Split into lines
    original_lines = original_content.splitlines()
    modified_lines = modified_content.splitlines()
    
    # Preprocess the file structure ONCE (this analyzes everything upfront)
    file_structure = preprocess_file(modified_lines, original_lines)
    
    # Print declarations found
    if verbose >= 2:
        print(f"  Preprocessed: {len(file_structure.declarations)} declarations found")
        log_file.write(f"  Preprocessed: {len(file_structure.declarations)} declarations found\n")        
        for name, (header_start, body_start, end) in file_structure.declarations.items():
            print(f"    - {name}: header={header_start+1}, body={body_start+1}, end={end+1}")
            log_file.write(f"    - {name}: header={header_start+1}, body={body_start+1}, end={end+1}\n")
        
    # Total counteir for removed lines across all rounds
    total_removed_count = 0
    round_num = 1
        
    # Initialize verification cache
    verification_cache = {}  # map from sha1 of file contents to verification result

    # Initialize set of declarations to remove because reference count is zero
    remove_decls : set[str] = set()

    # Lists of declaration names that have changes in body/spec 
    modified_decl_body = set()
    modified_decl_spec = set()

    # Initial population of modified declarations based on line_info
    for info in file_structure.line_info:
        if info.is_removable:
            enclosing_decl =  info.enclosing_method or info.enclosing_function
            if enclosing_decl is not None:
                if info.enclosing_location == "B":
                    modified_decl_body.add(enclosing_decl)
                elif info.enclosing_location == "S":
                    modified_decl_spec.add(enclosing_decl)
                elif info.enclosing_location == "H":
                    total_refs = sum(
                        cnt for (dep, depd), cnt in file_structure.dependencies.items() 
                        if depd == enclosing_decl
                    )
                    if total_refs == 0:
                        remove_decls.add(enclosing_decl)

    # Print dependencies
    if verbose >= 2:
        print("  Declaration dependencies:")
        log_file.write("  Declaration dependencies:\n")
        for (dependent, dependee), count in file_structure.dependencies.items():
            print(f"    - {dependent} depends on {dependee}: {count} times") 
            log_file.write(f"    - {dependent} depends on {dependee}: {count} times\n")   
    

    # Main simplification loop - multiple rounds until no more removals
    while True:
        if verbose >= 1:
            print(f"\n========== Round {round_num} ==========")
            log_file.write(f"\n========== Round {round_num} ==========\n")
        
        # print current modified/specified declarations
        if verbose >= 2:
            print(f"  Modified declaration bodies: {modified_decl_body}")
            log_file.write(f"  Modified declaration bodies: {modified_decl_body}\n")
            print(f"  Modified declaration specs: {modified_decl_spec}")
            log_file.write(f"  Modified declaration specs: {modified_decl_spec}\n")
            print(f"  Declarations marked for removal: {remove_decls}")
            log_file.write(f"  Declarations marked for removal: {remove_decls}\n")

        # Count of removals this round
        round_removed_count = 0

        # Iterate through lines using preprocessed info, backwards
        k = len(file_structure.line_info)
        info = None
        enclosing_decl = None
        new_modified_decl_body = False
        new_modified_decl_spec = False
        while k >= 0:
            # update list of modified declarations, when passing back from header lines            
            if info is not None and enclosing_decl is not None and info.enclosing_location == "H":            
                if not new_modified_decl_body and enclosing_decl in modified_decl_body:
                    modified_decl_body.discard(enclosing_decl)
                    if verbose >=2:
                        print("Removing from modified body: ", enclosing_decl)
                        log_file.write("Removing from modified body: " + enclosing_decl + "\n")
                if not new_modified_decl_spec and enclosing_decl in modified_decl_spec:
                    modified_decl_spec.discard(enclosing_decl)
                    if verbose >=2:
                        print("Removing from modified spec: ", enclosing_decl)
                        log_file.write("Removing from modified spec: " + enclosing_decl + "\n")
                new_modified_decl_body = False
                new_modified_decl_spec = False                
            
            # Ensure k is within bounds
            if k >= len(file_structure.line_info):
                k = len(file_structure.line_info) - 1           
            if k <= 0:
                break
            k -= 1
            info = file_structure.line_info[k]
            
            # enclosing decl  
            enclosing_decl = info.enclosing_method or info.enclosing_function

            # Skip trivial lines (blanks, etc.), or lines that match original, etc.
            if not info.is_removable:
                continue

            # Skip if declaration is marked for removal, and not reached header yet
            if enclosing_decl is not None and info.enclosing_location != "H" and enclosing_decl in remove_decls: 
                continue 

            # Determine the segment to remove
            start_index = info.line_num
            end_index = info.block_end if info.block_end >= start_index else start_index
            replace_with = info.replace_with
            remove_segment = "\n".join(file_structure.lines[start_index:end_index+1])

            # check if there are modifications that make it worth removing this segment
            recheck = False
            if enclosing_decl is None:
                recheck = True  # global scope changes always rechecked
            elif info.enclosing_location  == "H":
                recheck = enclosing_decl in remove_decls
            elif enclosing_decl in modified_decl_body or enclosing_decl in modified_decl_spec:
                recheck = True
            else:
                # check if there is any dependency that justifies recheck
                for (dependent, dependee) in file_structure.dependencies:
                    if dependent == enclosing_decl and dependee in modified_decl_spec:
                        recheck = True
                        break
                    if (dependee == enclosing_decl and info.enclosing_location == "S"
                        and (dependent in modified_decl_spec or dependent in modified_decl_body)):
                        recheck = True
                        break

            if not recheck:
                if verbose >= 2:
                    print(f"{enclosing_decl}: skipped: {remove_segment}")
                    log_file.write(f"{enclosing_decl}: skipped: {remove_segment}\n")
                continue

            # Create simplified lines without this segment
            new_lines = file_structure.lines[:start_index]
            if replace_with is not None:
                new_lines.append(replace_with)
            new_lines.extend(file_structure.lines[end_index + 1:])
    
            # Check if the simplified file passes verification
            # (Skip verification for comment-only removals)
            if not (end_index == start_index and remove_segment.strip().startswith("//")):
                cached = False
                contents = "\n".join(new_lines)
                # Check cache
                key = sha1(contents.encode("utf-8")).hexdigest()
                if verification_cache is not None and key in verification_cache:
                    cached = True
                    success = verification_cache[key]
                else:
                    # Get the enclosing method for --filter-symbol
                    filter_symbol = None
                    if use_filter_symbol and info.enclosing_method is not None and info.enclosing_location == "B":
                        filter_symbol = info.enclosing_method
                    
                    # Don't need to handle negative tests if changes are within the body of a method
                    # that is not a text method (with 'test' or 'Test' in its name)
                    if (not file_structure.contains_negative_tests or 
                        (info.enclosing_method is not None and info.enclosing_location == "B" and
                         "test" not in info.enclosing_method.lower())):
                        handle_neg_tests = False
                    else:
                        handle_neg_tests = True

                    # Verify the simplified file
                    success = verify_dafny_file(contents, 
                                                handle_negative_tests=handle_neg_tests,
                                            filter_symbol=filter_symbol,
                                            timeout=verifier_timeout+round_num-1)
                    
                    # Put results in a cache from file contents to result
                    if verification_cache is not None: 
                        verification_cache[key] = success  

                # skip removal candidate if didn't pass verification
                if success != 1:
                    if verbose >= 1:
                        if cached:
                            print(f"{enclosing_decl}: kept (using cache): {remove_segment}")
                            log_file.write(f"{enclosing_decl}: kept (using cache): {remove_segment}\n")
                        else:
                            print(f"{enclosing_decl}: kept: {remove_segment}")
                            log_file.write(f"{enclosing_decl}: kept: {remove_segment}\n")
                    continue  

                # Update modified declarations tracking  
                if enclosing_decl is not None:
                    # Full declaration removal
                    if info.enclosing_location == "H":
                        new_modified_decl_body=False
                        new_modified_decl_spec=False
                        modified_decl_body.discard(enclosing_decl)
                        modified_decl_spec.discard(enclosing_decl) 
                        remove_decls.discard(enclosing_decl) 
                        # but referenced declarations could be rechecked ...
                    # Removal in body/spec
                    elif info.enclosing_location == "B":
                        new_modified_decl_body=True
                        modified_decl_body.add(enclosing_decl)
                    elif info.enclosing_location == "S":
                        new_modified_decl_spec=True
                        modified_decl_spec.add(enclosing_decl)

            if verbose >= 1:
                print(f"{enclosing_decl}: removed: {remove_segment}")
                log_file.write(f"{enclosing_decl}: removed: {remove_segment}\n")

            # update reference counters in dependencies (in place)
            dependencies = file_structure.dependencies
            if enclosing_decl is not None:
                for other_decl in file_structure.declarations.keys():
                    if other_decl == enclosing_decl or other_decl not in remove_segment:
                        continue
                    # Check if it is actually a call with parenthesis
                    pattern = rf'\b{other_decl}\s*\('
                    count = len(re.findall(pattern, remove_segment))
                    if count == 0:
                        continue
                    key = (enclosing_decl, other_decl)
                    dependencies[key] = dependencies.get(key, 0) - count
                    if verbose >= 2:
                        print(f"Decrementing dependency: {key} by {count}, new count: {dependencies[key]}")
                        log_file.write(f"Decrementing dependency: {key} by {count}, new count: {dependencies[key]}\n")
                    if dependencies[key] == 0:
                        # sum all dependencies to other_decl
                        total_refs = sum(
                            cnt for (dep, depd), cnt in dependencies.items() 
                            if depd == other_decl
                        )
                        if total_refs == 0:
                            remove_decls.add(other_decl)
                            if verbose >= 1:
                                print(f"{other_decl}: Marked for full removal due to 0 dependencies")
                                log_file.write(f"{other_decl}: Marked for full removal due to 0 dependencies\n")

            # If successful, incrementally update file structure
            file_structure  = update_after_removal(file_structure, k, start_index, end_index, replace_with, new_lines, dependencies)
            
            # May cause removal of previous line_infos (shifting others), so adjust k accordingly
            if k > len(file_structure.line_info):
                k = len(file_structure.line_info)
            while k > 0 and file_structure.line_info[k-1].line_num >= start_index:
                k -= 1

            if not (end_index == start_index and remove_segment.strip().startswith("//")):                
                removed_count = end_index - start_index + 1
                if replace_with is not None:
                    removed_count -= 1

                round_removed_count += (end_index - start_index + 1)
            
        # End of round - check if we made progress
        if round_removed_count == 0:
            if verbose >= 1:
                print(f"Round {round_num}: No more simplifications possible.")
                log_file.write(f"Round {round_num}: No more simplifications possible.\n")
            break

        if verbose >= 1:
            print(f"Round {round_num}: Removed {round_removed_count} lines.")
            log_file.write(f"Round {round_num}: Removed {round_removed_count} lines.\n")
        total_removed_count += round_removed_count
        
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
        log_file.write(f"\n========== COMPLETE ==========\n")
        log_file.write(f"Total rounds: {round_num}\n")
        log_file.write(f"Total lines removed: {total_removed_count}\n")

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
    total_time_seconds = 0

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
            log_file.write(f"Could not find stripped file for {filename}\n")
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
        log_file.write(f"\n{'='*60}\n")
        log_file.write(f"Simplifying {filename}\n")
        log_file.write(f"{'='*60}\n")
        
        # get timestamp
        timestamp_start = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())

        # simplify() now handles all rounds internally (single preprocessing)
        removed_lines_count = simplify(
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

        if end_filename and filename == end_filename:
            break

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
    simplify_folder(
        r"TODO", 
        r"TODO",
        r"TODO"
    )
