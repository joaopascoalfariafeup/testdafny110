
#### Parameters ####

# Path to the Dafny executable 
dafny_executable = r"TODO"

# Verbosity level (0: no output, 1: some output, 2: detailed output)
verbose = 1

# verifier timeout in seconds
verifier_timeout = 30

# handle negative tests (tests expected to fail verification, marked with //@invalid)
handle_negative_tests = True

#####  Imports ##### 
import os
import subprocess
import re

#### Dafny verification functions ####


# Verifies a Dafny file using the Dafny verifier
def verify_dafny_file(filepath, handle_negative_tests=handle_negative_tests) -> int:
    # run the verifier
    process = subprocess.Popen([dafny_executable,"verify", filepath,"--verification-time-limit:" + str(verifier_timeout),"--allow-warnings:true"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)     
    stdout, _ = process.communicate()

    # remove errors regarding counter-examples
    cleaned  = "\n".join(
      line for line in stdout.decode('utf-8').splitlines() 
      if not line.startswith("Prover error")
    )

    # check for errors in output
    if b"resolution/type errors" in stdout or b"parse errors" in stdout:
        return -1 # syntax errors        
    if not cleaned.endswith(' 0 errors'): 
        return 0 # verification failed
           
    # run negative tests if required
    if handle_negative_tests:
        # temporary file name for negative tests, replacing the final ".dfy" with "_negative.dfy"
        new_filepath = filepath[:-4] + "_negative.dfy"

        # read the Dafny code from the file to a lists of strings
        with open(filepath, 'r') as file:
            dafny_code = file.read()
        lines = dafny_code.splitlines()

        # iterate over the lines
        for index in range(len(lines)):
            # check it it is a negative test line
            line = lines[index]
            if not line.strip().startswith("//@invalid"):
                continue
            # erase this string in this line and save to file
            old_line = line
            lines[index] = line.replace("//@invalid", "")                 
            with open(new_filepath, 'w') as new_file:
                new_file.writelines('\n'.join(lines))
            # call the verifier again on the new file
            success = verify_dafny_file(new_filepath, False)
            # if passes, return failure
            if success == 1:
                return 0 # failure
            # otherwise restore the old line and continue
            lines[index] = old_line

    return 1 # success


#### Simplification functions ####

# Given a list of lines and a start index, returns the end index of a removable code fragment
# Are considered removable code fragments:
# - block statements starting with calc, if, for, while, forall, until matching braces
# - declarations starting with function, lemma, predicate, ghost function, ghost predicate until matching braces
# - assertions starting with assert and ending with ';'
# - equalities (inside calculational proofs) starting with '==' and ending with ';'
# - single lines otherwise (excluding empty lines, single braces, pairs of braces)
def get_removable_code_fragment(lines: list[str], start_index: int) -> tuple[int, str|None]:
    line = lines[start_index].strip()

    # ignore empty lines or single braces or pairs of braces
    if line == "" or line == "{" or line == "}" or re.sub(r'\s+', '', line) == "{}" :
        return start_index - 1, None

    # declaration initiators
    declaration_initiators = ["function", "lemma", "predicate", "ghost function", "ghost predicate"]
    declaration_initiators2 = declaration_initiators + ["method"]

    # if this line initiates a composite statement with {}, search for end of block (closing braces)
    block_initiators = ["calc ", "forall ", "if ", "else", "calc{", "if(", "for ", "while ", "while(", "by ", "} else"]
    if any(line.startswith(token) for token in block_initiators):
        if line.startswith("}"):
            close_brace_count = -1
        else:
            close_brace_count = 0
        open_brace_count = 0
        for i in range(start_index, len(lines)):
            line_to_check = lines[i]
            # if starts with a declaration initiator, aborts
            if i > start_index and any(line_to_check.strip().startswith(token) for token in declaration_initiators2):
                break            
            # if contains pattern 'multiset{...}', ignore that part of the line
            if 'multiset{' in line_to_check:
                parts = re.split(r'multiset\{.*?\}', line_to_check)
                line_to_check = ''.join(parts)
            # if contains pattern '{:fuel...}', ignore that part of the line 
            if '{:fuel' in line_to_check:
                parts = re.split(r'\{\:fuel [^}]+\}', line_to_check)
                line_to_check = ''.join(parts)
            open_brace_count += line_to_check.count('{')
            close_brace_count += line_to_check.count('}')
            if (open_brace_count == close_brace_count and open_brace_count > 0
            and not "else" in line_to_check 
            and not (i < len(lines)-1 and "else" in lines[i+1])):
                replace_with = None
                if line.startswith("} else"):
                    # tells that, after removing, has to insert "}" with leading original spaces
                    replace_with = re.match(r'^\s*', lines[start_index]).group(0) + "}"
                if line.startswith("by "):
                    # tells that, after removing, has to insert ";" 
                    replace_with = re.match(r'^\s*', lines[start_index]).group(0) + ";"
                return i, replace_with
    # if this line initiates a statement that ends with ';', check end of statement
    if (line.startswith("assert ") or line.startswith("==")) and not line.endswith(";") and not "//" in line:
        i = start_index + 1
        while i < len(lines) and not (lines[i].strip().endswith(";") or "//" in lines[i]):
            i += 1
        if i < len(lines):
            return i, None

    # if this line initiates a declaration, find end of declaration
    if any(line.startswith(token) for token in declaration_initiators):
        open_brace_count = 0
        close_brace_count = 0
        for i in range(start_index, len(lines)):
            line_to_check = lines[i]   
            # if contains pattern 'multiset{...}', ignore that part of the line
            if 'multiset{' in line_to_check:
                parts = re.split(r'multiset\{.*?\}', line_to_check)
                line_to_check = ''.join(parts)
            # if contains pattern '{:fuel...}', ignore that part of the line 
            if '{:fuel' in line_to_check:
                parts = re.split(r'\{\:fuel [^}]+\}', line_to_check)
                line_to_check = ''.join(parts)
            # if starts with a new initiator, aborts
            if i > start_index and any(line_to_check.strip().startswith(token) for token in declaration_initiators2):
                break            
            # count braces
            open_brace_count += line_to_check.count('{')
            close_brace_count += line_to_check.count('}')
            if open_brace_count == close_brace_count and open_brace_count > 0:
                return i, None

    # avoid removing closing braces alone
    if line.startswith("}"):
        return start_index, None
    
    # otherwise, try this single line
    return start_index, None

   
# Simplify a Dafny file by removing lines not present in the original file and checking it still verifies.
def simplify(original_file: str, modified_file: str, simplified_file: str, start_from_simplified_file: bool = False) -> int:    
    # read original file
    with open(original_file, 'r', encoding='utf-8') as file:
        original_content = file.read()    
   
    # read modified file
    with open(modified_file, 'r', encoding='utf-8') as file:
        modified_content = file.read()
    
    # read current simplified file, if existent
    simplified_content = None
    if os.path.exists(simplified_file):
        with open(simplified_file, 'r', encoding='utf-8') as file:
            simplified_content = file.read()

    # if starting from simplified file, use its content
    if start_from_simplified_file:
        if simplified_content is not None:
            modified_content = simplified_content
        else:
            print(f"Could not find simplified file {simplified_file} to start from.")
            return 0

    # strip and remove spaces in original lines, for more robust comparison
    original_lines = original_content.splitlines()
    original_lines_stripped = [ re.sub(r'\s+', '', re.sub(r'\{\:fuel [^}]+\}\s*', '', line)) for line in original_lines]
    original_index = 0

    # split modified into lines
    modified_lines = modified_content.splitlines()

    # check if it contains negative tests
    contains_negative_tests = any(line.strip().startswith("//@invalid") for line in modified_lines)

    # counter removed lines
    removed_lines_count = 0

    # iterate modified lines, and try to remove one or two at a time if not present (striped) in original
    k = 0
    while k < len(modified_lines):
        line = modified_lines[k]

        # stripped and without spaces and fuel for comparison
        line_stripped = re.sub(r'\s+', '', re.sub(r'\{\:fuel [^}]+\}\s*', '', line))

        # ignore trivial lines
        if line_stripped == "" or line_stripped == "{" or line_stripped == "}" or line_stripped == "{}":
            k += 1
            continue

        # if present in original lines (from last mateched line onwards), skip
        found = False
        for i in range(original_index, len(original_lines_stripped)):
            if line_stripped == original_lines_stripped[i]:
                found = True
                original_index = i + 1
                break            

        if found:
            k += 1
            continue

        # if not found, try to remove a block or statement starting at this line
        start_index = k
        end_index, replace_with = get_removable_code_fragment(modified_lines, start_index)
        if end_index < start_index:
            k += 1
            continue

        # create simplified lines without this block and save it for logging
        new_lines = modified_lines[:]
        remove_segment = "\n".join(new_lines[start_index:end_index+1])
        del new_lines[start_index:end_index+1]

        # if need to replace with something, do it
        if replace_with is not None:
            new_lines.insert(start_index, replace_with)

        # save to simplified file 
        with open(simplified_file, 'w', encoding='utf-8') as file:
            file.write("\n".join(new_lines))

        # check if the simplified file failes verification
        if not (end_index == start_index and remove_segment.strip().startswith("//")):
            success = verify_dafny_file(simplified_file, handle_negative_tests=contains_negative_tests) 
            if success != 1:
                print("Could not remove segment: " + remove_segment)
                k += 1
                continue           
            
        # if successful, update modified_lines with new_lines, and continue on same index
        modified_lines = new_lines
        print(f"Removed not needed segment: {remove_segment}")
        removed_lines_count += (end_index - start_index + 1)

    # if nothing could be removed, clean up and return
    if removed_lines_count == 0:
        if not start_from_simplified_file:
            os.remove(simplified_file)
        else:
            with open(simplified_file, 'w', encoding='utf-8') as file:
                file.write("\n".join(modified_lines))
        return 0   

    # if lines removed, save the simplified content
    with open(simplified_file, 'w', encoding='utf-8') as file:
        file.write("\n".join(modified_lines))

    # return the number of removed lines
    simplified_content = "\n".join(modified_lines)
    return removed_lines_count

# Tries to simplify all Dafny files in a folder with modified files ending in "_NN_llm.dfy". 
# Considers as original files files with same name but ending in "_stripped.dfy" in another folder.
# Saves the simplified files in a third folder, with names ending in "_NN_llm_simplified.dfy".
def simplify_folder(folder_with_stripped_files: str, folder_with_modified_files: str, folder_with_simplified_files: str, start_filename: str = None, end_filename: str = None, restrict_to_set = None, start_from_simplified_files: bool = False) -> tuple[int, int]:
    # counter for total simplified files and total removed lines
    total_simplified_files = 0
    total_removed_lines = 0
    start = False if start_filename is not None else True

    # loop through the files in the input folder
    for filename in os.listdir(folder_with_modified_files):
        # restrict to files generated with llm
        if not filename.endswith('_llm.dfy'):
            continue
        # if there is a start filename, wait until it is found
        if not start:
            if filename == start_filename:
                start = True
            else:
                continue
        # if there is a restrict set, skip files not in the set
        if restrict_to_set is not None and filename not in restrict_to_set:
            continue
        # search stripped file, replacing "_(number)_llm.dfy" with "_stripped.dfy"
        match = re.match(r'^(.*)_\d+_llm\.dfy$', filename)
        if not match:
            print(f"Could not find stripped file for {filename}")
            # if there is an end filename, check if it is reached
            if end_filename and filename == end_filename:
                break
            else:
                continue
        # get the stripped filename
        base_name = match.group(1)
        stripped_filename = f"{base_name}_stripped.dfy"

        # build full file paths
        filepath_modified = os.path.join(folder_with_modified_files, filename)
        filepath_stripped = os.path.join(folder_with_stripped_files, stripped_filename)
        filepath_simplified = os.path.join(folder_with_simplified_files, filename.replace('_llm.dfy', '_llm_simplified.dfy'))

        # simplify the file iteratively until no more lines can be removed
        round = 1
        removed_lines_count = 0
        start_from_simplified = start_from_simplified_files
        while True: 
            print(f"Simplifying {filename}, round {round}")
            count = simplify(filepath_stripped, filepath_modified, filepath_simplified, start_from_simplified_file=start_from_simplified)
            round += 1
            if count == 0:
                break
            removed_lines_count += count
            filepath_modified = filepath_simplified
            start_from_simplified = True

        # print result for this file
        if removed_lines_count > 0:
            print(f"{filename}: Simplified by removing {removed_lines_count} lines")
            total_simplified_files += 1
            total_removed_lines += removed_lines_count
        else:
            print(f"{filename}: Could not be simplified")

        # if there is an end filename, check if it is reached
        if end_filename and filename == end_filename:
            break

    # print total results
    print(f"Total simplified files: {total_simplified_files}, total removed lines: {total_removed_lines}")
    return total_simplified_files, total_removed_lines



simplify_folder(r"TODO", r"TODO", r"TODO")