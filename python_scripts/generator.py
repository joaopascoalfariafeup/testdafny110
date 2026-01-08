# This file contains a script for assessing the capabilities of LLMs to
# generate features required for verifying programs in Dafny (pre-conditions, 
# post-conditions, loop invarints and auxiliary functions and predicates, and proof helpers).  
# The script processes a dataset of Dafny files with complete solutions, 
# removing the features to be generated, and then uses LLMs to generate them.
# The script then verifies the generated files using the Dafny verifier.
# The script outputs a CSV file with the results of the verification process.
# The script also outputs a log file with the results of the processing.

####### Initial definitions #######

# Enumeration of supported APIs
class API:
    OpenAI = 1
    Antrophic = 2
    DeepSeek = 3

# Data structure with API, model, temperature (0=default), and minimum and maximum attempts
class LLMData:
    def __init__(self, api, model, temperature, min_attempts, max_independent_attempts, max_attempts):
        self.api = api
        self.model = model
        self.temperature = temperature
        self.min_attempts = min_attempts
        self.max_independent_attempts = max_independent_attempts
        self.max_attempts = max_attempts

####### Configuration parameters #######

# Folder with source files in Dafny (with extension .dfy)
input_folder = r"TODO: specify input folder"

# Folder to place generated files in Dafny (different from the previous folder)
output_folder_base = r"TODO: specify output folder"

# API keys
openai_key = r"TODO: specify OpenAI API key"
antrophic_key = r"TODO: specify Anthropic API key"
deepseek_key = r"TODO: specify DeepSeek API key"

# Path to the Dafny executable 
dafny_executable = r"TODO: specify Dafny executable path"

# Verbosity level (0: no output, 1: some output, 2: detailed output)
verbose = 1

# verifier timeout in seconds
verifier_timeout = 60

# remover lemas and lines marked as helper 
remove_lemmas = True
remove_helpers = True

# LLMs to try with temperature and number of attempts (uncomment the one to be used)
llms = [LLMData(API.Antrophic, "claude-opus-4-5", 0.5, 1, 1, 10)] 
#llms=[LLMData(API.OpenAI, "gpt-5.2", 0.5, 1, 1, 10)]
#llms = [LLMData(API.DeepSeek, "deepseek-chat", 0.5, 1, 1, 2)]
#llms = [LLMData(API.OpenAI, "gpt-4-0613", 0.5, 0, 0, 4)]

#####  Imports ##### 
import os
import subprocess
from openai import OpenAI
import traceback
import time
import anthropic
import re

#####  Prompts #####

base_prompt = """
You are an expert in the Dafny programming language and formal verification.  
Your task is to insert any missing pre-conditions ('requires' clauses), post-conditions ('ensures' clauses), loop invariants ('invariant' clauses) and any auxiliary ghost predicates, ghost functions, and proof helpers (assertions and lemmas) needed for successful verification of the provided Dafny code, following these specific instructions.

Task Requirements:
- The Dafny code will be enclosed between the tags BEGIN DAFNY and END DAFNY.
- Do not change the original Dafny code! Your task is just to insert 'requires', 'ensures', and 'invariant' clauses (plus auxiliary ghost predicates, ghost functions, and proof helpers, if needed).
- Do not provide any explanations or comments in your output; only output the modified code between the tags BEGIN DAFNY and END DAFNY.

Follow Dafny syntax rules:
- Method preconditions and postconditions must be placed immediately after the method header and before the method body, as in:
   method Abs(x: int) returns (y: int)
     requires true
     ensures y >= 0
     ensures x == y || x == -y
   {
     if x < 0 { return -x; } else { return x; }
   }
- Loop invariants must be placed immediately after the loop header and before the loop body, as in:
   while i < n
     invariant 0 <= i <= n
   {
     ...
     i := i + 1;
   }
- Use '==>' for logical implication.
- Use |s| for sequence length and a.Length for array length.
- Do not use dot operations on collections like s.Map, s.Contains, s.Min, etc.
- Do not use aggregate functions on collections, like max, min, and sum, unless they are defined in the code.   
- Do not invoke methods inside pre/post-conditions (only functions and predicates can be invoked).
- Use "if then else " for ternary expressions instead of " ? : ".
- The syntax 'function' (specification) 'by method' (implementation) is valid in Dafny.
    
Guidelines for writing pre/post-conditions (requires and ensures clauses):
- Do not add pre/post-conditions to test methods or the Main method.
- Do not add pre/post-conditions for methods defined with 'by method' (as they are inherited from the function/predicate definition).
- Do not add redundant conditions like 'requires true' or 'ensures true'.
- Do not add null checks like 'requires x != null', because by default reference types in Dafny do not accept null.
- Write pre/post-conditions that capture all relevant constraints.
- For requires clauses, specify necessary conditions for the method to work correctly.
- For ensures clauses, thoroughly establish the ranges and constraints that the returned values and output parameters must satisfy.
- Where possible, use quantified expressions (easier to verify) instead of recursive definitions.
- Always provide explicit lower bounds in quantifiers like forall k :: 0 <= k <= n, instead of forall k :: k < n.
- When a method modifies an array ('modifies' clause), consider what parts of the array change and what parts remain unchanged.
- When a method updates object fields, the ensures clause should describe the relationship between pre-state (old) and post-state values.
- If needed for writing thorough pre/post-conditions, you can create auxiliary ghost functions and predicates (namely for recursive definitions).
- In case you need to create a recursive function, make sure that the direction of recursion matches the implementation being verified.
  Example of preferred form if implementation iterates from lower to higher indices: ghost function Sum(s: seq<int>): int {if |s| == 0 then 0 else s[|s|-1] + Sum(s[..|s|-1])}    
  Example of form to avoid: ghost function Sum(s: seq<int>): int {if |s| == 0 then 0 else s[0] + Sum(s[1..])}    
- If there are test assertions on lists (sequences, arrays, strings) and the postconditions under test involve recursive functions, you can set the fuel attribute to the list length as in {:fuel n} to facilitate verification.
  
Guidelines for writing loop invariants:
- Try to create loop invariants with a structure similar to the method post-conditions ('ensures' clause), reusing auxiliary functions or predicates mentioned in those clauses, to be incrementally enforced as the loop progresses.
- Do not reference uninitialized variables or output parameters in the invariants.
- You must first understand the role of each variable in the algorithm, using any comments provided, to properly construct meaningful invariants.
- Create separate invariants for each variable manipulated within the loop, ensuring that each is well-defined.
- Do not include redundant or overly generic invariants.
- Where applicable, prefer sequence operations over quantifiers on arrays.
- Always provide explicit lower bounds in quantifiers like forall k :: 0 <= k <= n, instead of forall k :: k < n.
- When a loop in a method modifies an array ('modifies' clause), a loop invariant should exist for each segment unchanged up to the current iteration, using old().
- 'for' loops do not need a 'decreases' clause nor a loop invariant for the loop index bounds, as they are automatic.
- When 'boolean' variables are manipulated in a loop, the loop invariants should describe the conditions upon which they may be true and false (covering both cases).
- In 'for' loops, the upper bound is exclusive.
- In the case of descending for loops ('downto'), the loop iterator is implicitly decremented at the beginning of the loop body (not at the end).
- If needed, you can also add 'decreases' clauses to help prove loop termination (in most cases, they are inferred by Dafny).

Failure to follow these instructions strictly will result in incorrect output.
"""

repair_prompt = """
Fix the preconditions, postconditions, and loop invariants (and any other needed annotations, like ghost functions, ghost predicates, assertions and lemmas) in the following program in Dafny so that it can be verified successfully without any errors.
The program contains one or more methods under verification, one or more test methods with test assertions, and possible auxiliary declarations (functions, predicates, etc.).

Task Requirements:
- The Dafny code will be enclosed between the tags BEGIN DAFNY and END DAFNY.
- Current verification errors will be enclosed between the tags BEGIN VERIFICATION ERRORS and END VERIFICATION ERRORS.  
- Output the modified code between the tags BEGIN DAFNY and END DAFNY.
- Do not change assertions of test outputs in the test methods! (but you can add/fix proof helpers if needed)
- Do not change the Dafny program under verification (namely the algorithms in method bodies); your role is just to fix the annotations needed for successful verification!
- Do not use 'assume' (unproved) statements!
- Do not use 'decreases *' clauses to circumvent verification of termination!
- Follow these steps:
  1) Understand the program and the specification and verification annotations;
  2) Understand the errors; 
  3) Determine the root causes of the errors and possible fixes (using hints below when applicable).

Hints for fixing verification errors:  
1) Test assertions serve as oracles for postconditions, which in turn serve as oracles for loop invariants:
  - If test assertions verify successfully, the postconditions are likely correct;
  - If test assertions fail to verify, the postconditions may be too weak or incorrect, or proof helpers are needed to check the test assertions (e.g., additional assertions or lemmas);
  - If postconditions verify successfully, the loop invariants are likely correct;
  - If postconditions fail to verify, the loop invariants may be insufficient or need proof helpers
  - For nested loops, outer loop invariants serve as oracles for inner loop invariants.
2) Ordering-preserving postconditions are often required for tests to pass; they are best defined using an auxiliary sequence comprehension function, such as (with filtering function 'f' and mapping function 'g'):
    ghost function seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
    {
      if s == [] then []
      else if f(s[|s|-1]) then seqc(s[..|s|-1], f, g) + [g(s[|s|-1])]
      else seqc(s[..|s|-1], f, g)
    }
3) Sometimes the solution is correct, but additional proof helpers are required by the Dafny verifier, such as:
a) Provide assertions to help Dafny prove properties involving lists (sequences, arrays or strings), such as:
    assert a[..i+1] == a[..i] + [a[i]];  // appending
    assert a[..i] == a[..k] + a[k..i]; // concatenation
    assert a[..] == a[..a.Length]; // length
b) Provide (non-recursive) postconditions in recursive function definitions, as in:
    ghost function min(s: seq<int>): int
      requires |s| > 0
      ensures min(s) in s && forall k :: 0 <= k < |s| ==> s[k] >= min(s)
    { if |s| == 1 then s[0] else if s[|s|-1] < min(s[..|s|-1]) then s[|s|-1] else min(s[..|s|-1])}
c) If test assertions fail on lists of length N (sequences, arrays or strings) and the postconditions of the method under test involve recursive functions, the first thing to do is to set the fuel attribute to {:fuel N} in the recursive function, as in:
    ghost function {:fuel 5} min(s: seq<int>): int (...)
d) If the verifier warns that it could not find a trigger for a quantifier,  instead of adding a {:trigger} attribute, extract the complex part of the body to an auxiliary predicate, as in:
    Replace: exists i ::  ... complex_expression(args) ...  
    With: ghost predicate p(args) { complex_expression(args) }
          exists i:: ... p(args) ...
e) In recursive function definitions, make sure that the order of recursion is the opposite of the order of iteration in the implementation being verified, to facilitate verification.
4) Sometimes additional proof helpers are needed in the test methods, to help prove the test assertions on test outcomes, such as:
a) Provide auxiliary assertions on the content of arrays to help trigger verification, as in:
    var a := new int[] [1, 3, 5];
    assert a[..] == [1, 3, 5]; // helper
    assert a[0] == 1 && a[1] == 3 && a[2] == 5; // alternative helper 
b) Provide auxiliary assertions with concrete examples, counter examples or intermmediate results to convince Dafny of the test outcomes (just before the assertion that checks the test outcomes).
c) Only if previous options don't work, provide auxliary lemmas proving the uniqueness of test results.
"""


######## Global initializations ########

# create output folder
output_folder = output_folder_base + "/" + llms[0].model + " - " + str(llms[0].temperature) + " - " + time.strftime(r"%Y-%m-%d %H-%M")
os.makedirs(output_folder, exist_ok=True)

# initialize the log file
log_file = open(output_folder + r"\_log.txt", "w")

# initialize the API clients
clientOpenAI = OpenAI(api_key = openai_key)
clientAnthropic = anthropic.Anthropic(api_key = antrophic_key)
clientDeepSeek = OpenAI(api_key = deepseek_key, base_url = "https://api.deepseek.com/v1")

######## Dany file merging ########

# Merges the contents of two files (represented as strings) without duplicating common lines.
# Returns the merged content as a list of lines.
def merge_files(file1, file2):
    file1_lines = file1.split('\n')
    file2_lines = file2.split('\n')
    merged_lines = []
    index1 = 0
    index2 = 0
    while index1 < len(file1_lines) and index2 < len(file2_lines):
        # get the next lines from each file to local variables
        line1 = file1_lines[index1]
        line2 = file2_lines[index2]

        # remove all whitespaces from each line for code comparison purposes
        line1_stripped = line1.strip().replace(" ","")
        line2_stripped = line2.strip().replace(" ","")
        
        # remove all characters after '//' in each line (in case they appear)
        if '//' in line1_stripped:
            line1_stripped = line1_stripped[:line1_stripped.index('//')]
        if '//' in line2_stripped:
            line2_stripped = line2_stripped[:line2_stripped.index('//')]
        
        # compare ignoring spaces and comments (lines starting with '//')
        if line1_stripped == line2_stripped:
            merged_lines.append(line1)
            index1 += 1
            index2 += 1
        elif line1.strip() == "":
            index1 += 1
            merged_lines.append("")
        elif line2.strip() == "":
            index2 += 1
            merged_lines.append("")
        else:
            # find the nearest subsequent matching line in file2
            found2 = -1
            for i in range(index2 + 1, len(file2_lines)):
                if file1_lines[index1].strip().replace(" ","") == file2_lines[i].strip().replace(" ",""):
                    found2 = i
                    break

            # find the nearest subsequent matching line in file1
            found1 = -1
            for i in range(index1 + 1, len(file1_lines)):
                if file1_lines[i].strip().replace(" ","") == file2_lines[index2].strip().replace(" ",""):
                    found1 = i
                    break
            
            if found1 == -1 and found2 == -1:
                if index1 < index2:
                    merged_lines.append(file1_lines[index1])
                    index1 += 1
                else:
                    merged_lines.append(file2_lines[index2])
                    index2 += 1
            elif found1 == -1 :
                for i in range(index2, found2):
                    merged_lines.append(file2_lines[i])
                    index2 += 1
            elif found2 == -1:
                for i in range(index1, found1):
                    merged_lines.append(file1_lines[i])
                    index1 += 1
            else:
                if found1 < found2:
                    for i in range(index1, found1):
                        merged_lines.append(file1_lines[i])
                        index1 += 1
                else:
                    for i in range(index2, found2):
                        merged_lines.append(file2_lines[i])
                        index2 += 1

    # add the remaining lines from any of the files
    if index1 < len(file1_lines):
        merged_lines.extend(file1_lines[index1:])
    if index2 < len(file2_lines):
        merged_lines.extend(file2_lines[index2:])

    return "\n".join(merged_lines)

tokens_spent = 0

######## Stripping specification and verification annotations from a Dafny file ########

# Remove pre/post-conditions, loop invariants and ghost functions and predicates
# from a Dafny file and saves the result to a new file
def remove_prepostinv_lines_and_save(filepath, remove_loopinv = True, remove_prepost = True, remove_ghost_func_pred=True):
    # Get filename from filepath
    filename = os.path.basename(filepath)

    # Determine the new filename by appending 'stripped' before the .dfy extension
    new_filename = f"{filename[:-4]}_stripped.dfy"

    # Determine the new filepath by joining the output folder and the new filename
    new_filepath = os.path.join(output_folder, new_filename)
    
    # Read the lines of the source file
    with open(filepath, 'r') as file:
        lines = file.readlines()

    old_len = len(lines)

    # Remove ghost functions and predicates
    if remove_ghost_func_pred:
        i = 0
        while i < len(lines):
            # check if the line starts with a comment or ghost or lemma
            if lines[i].strip().startswith('//') or lines[i].strip().startswith('ghost ') or (remove_lemmas and lines[i].strip().startswith('lemma')):
                # skip commented lines
                j = i
                while j < len(lines) and lines[j].strip().startswith('//'):
                    j += 1 
                # check if it is a ghost function or predicate or lemma
                if lines[j].strip().startswith('ghost function') or lines[j].strip().startswith('ghost predicate') or (remove_lemmas and lines[j].strip().startswith('lemma')):   
                    k = j
                    # go to the end of the ghost function or predicate or lemma definition
                    while k < len(lines) and not lines[k].startswith('}'): # assumes no indentation of final }
                        k += 1
                    # remove the ghost function or predicate and the following lines until the closing brace
                    lines = lines[:i] + lines[k+1:]
                else:
                    i = j + 1
            else:
                i = i + 1 


    # remove lines starting with 'invariant' or'decreases' (loop invariants and variants)
    if remove_loopinv:
        lines = [line for line in lines if not line.strip().startswith("invariant") and not line.strip().startswith("decreases")]

    # remove lines commented with // helper
    if remove_helpers:
        lines = [line for line in lines if not re.search(r'//.*helper.*', line)]

    # Remove pre/post-conditions of methods (after the header and before opening brace)
    if remove_prepost:
        new_lines = []
        after_header = False 
        for i in range(len(lines)):
            line = lines[i]
            if line.strip().startswith("method") and not line.strip().endswith("{"):
                after_header = True 
            elif after_header and line.strip().startswith("{"):
                after_header = False
            if not (after_header and (line.strip().startswith("requires") or line.strip().startswith("ensures"))):
                new_lines.append(line)
        lines = new_lines


    # if none removed, just terminate and return None
    if len(lines) == old_len:
        return None
    
    # Write the filtered lines to the new file in output folder
    with open(new_filepath, 'w') as new_file:
        new_file.writelines(lines)
        
    if verbose > 1:    
        print(f"Stripped file saved to {new_filepath} and {new_filepath}.")
    log_file.write(f"Stripped file saved to {new_filepath} and {new_filepath}.\n")

    return new_filepath

####### Dafny file verification #######

# Regex to match: assert var == exp1 || var == exp2;
disjunctive_asssert_pattern = re.compile(
        r'^\s*assert\s+(\w+)\s*==\s*(.+?)\s*\|\|\s*\1\s*==\s*(.+?)\s*;\s*$')

# Verifies a Dafny file using the Dafny verifier
def verify_dafny_file(filepath, split_disjunctive_test_assertions = False, handle_negative_tests = True):
    # run the verifier
    process = subprocess.Popen([dafny_executable,"verify", filepath,"--verification-time-limit:" + str(verifier_timeout),"--allow-warnings:true"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)     
    stdout, _ = process.communicate()

    # save the output messages to the log file
    if log_file:
        log_file.write(stdout.decode('utf-8'))

    # remove errors regarding counter-examples
    cleaned = "\n".join(
      line for line in stdout.decode('utf-8').splitlines() 
      if not line.startswith("Prover error")
    )

    # determine outcome
    if b"resolution/type errors" in stdout or b"parse errors" in stdout:
        return -1, cleaned, 0 # syntax errors
    elif cleaned.endswith(' 0 errors'):
        if split_disjunctive_test_assertions:
            # Read the Dafny code from the file to a string
            with open(filepath, 'r') as file:
                dafny_code = file.read()
            lines = dafny_code.splitlines()

            after_test = False

            # new dafny file replacing the final ".dfy" with "_split.dfy"
            new_filepath = filepath[:-4] + "_split.dfy"
            num_errors = 0

            # iterated with a line counter over the lines
            for line in lines:
                # Check if we reached a test section (line containg Test or test)
                if line.find("method") != -1 and (line.find("Test") != -1 or line.find("test") != -1):
                    after_test = True
                if not after_test:
                    continue                 
                match = disjunctive_asssert_pattern.match(line)
                if not match:
                    continue
                var, exp1, exp2 = match.groups()
                index = lines.index(line)
                original_line = line
                for exp in [exp1, exp2]:
                    new_assert = f"assert {var} == {exp};";
                    # replace the line with these assertions
                    lines[index] = new_assert
                    # write message to log file and console
                    if verbose > 1:
                        print(f"Split disjunctive assertion in line: {line} into: {new_assert}")
                    log_file.write(f"Split disjunctive assertion in line: {line} into: {new_assert}\n")
                    # write the modified lines to the new file
                    with open(new_filepath, 'w') as new_file:
                        new_file.writelines('\n'.join(lines))
                    # call the verifier again on the new file
                    success, _, _ = verify_dafny_file(new_filepath, False, False)
                    # if passes, append error and return failure
                    if success == 1:
                        cleaned = cleaned + f"\nError: the postcondition seems too strong, because it should allow any of the values in the disjunctive test assertion \n {original_line}\nand not restrict to one of the possible values.\n" 
                        print (cleaned)
                        num_errors = num_errors + 1
                # restore the old line
                lines[index] = original_line
            if num_errors > 0:
                return 0, cleaned, num_errors # failure
        
        if handle_negative_tests:
            # Read the Dafny code from the file to a string
            with open(filepath, 'r') as file:
                dafny_code = file.read()
            lines = dafny_code.splitlines()

            after_test = False

            # new dafny file replacing the final ".dfy" with "_negative.dfy"
            new_filepath = filepath[:-4] + "_negative.dfy"
            num_errors = 0

            # iterated with a line counter over the lines
            for line in lines:
                # Check if we reached a test section (line containg Test or test)
                if line.find("method") != -1 and (line.find("Test") != -1 or line.find("test") != -1):
                    after_test = True
                if not after_test:
                    continue                 
                if line.strip().startswith("//@invalid"):
                    # erase this string in the line
                    index = lines.index(line)
                    old_line = line
                    new_line = line.replace("//@invalid", "")
                    lines[index] = new_line
                    with open(new_filepath, 'w') as new_file:
                        new_file.writelines('\n'.join(lines))
                    # call the verifier again on the new file
                    success, _, _ = verify_dafny_file(new_filepath, False, False)
                    # restore the old line
                    lines[index] = old_line
                    # if passes, append error and return failure
                    if success == 1:
                        cleaned = cleaned + f"\nError: the assertion\n {old_line}\n was expected to fail but passed verification. \n Probably the preconditions are too weak or the postconditions are too strong." 
                        print (cleaned)
                        num_errors = num_errors + 1
            if num_errors > 0:
                return 0, cleaned, num_errors # failure
        return 1, cleaned, 0 # success
    else:    
        m = re.search(r"(\d+)\s+error", cleaned)
        num_errors = int(m.group(1)) if m else 0
        m = re.search(r"(\d+)\s+verified", cleaned)
        num_verified = int(m.group(1)) if m else 0
        m = re.search(r"(\d+)\s+timeout", cleaned)
        num_timeout = int(m.group(1)) if m else 0
        return 0, cleaned, (10 - num_verified)*10 + num_errors + num_timeout * 100# failure


####### LLM processing #######
def call_llm(task_id, llm_data, system_prompt, user_prompt):
    try:
        start_time_api_call = time.time()

        if llm_data.api == API.OpenAI:
            if llm_data.model.startswith("gpt-5"):
                response = clientOpenAI.responses.create(
                    model=llm_data.model,
                    input=system_prompt + "\n\n" + user_prompt,
                    reasoning={"effort": "low"},
                    text={"verbosity": "low"}
                )
                #extract text
                output = ""
                for item in response.output:
                    if hasattr(item, "content") and item.content is not None:
                        for content in item.content:
                            if hasattr(content, "text") and content.text is not None:
                                output += content.text
            else:
                response = clientOpenAI.chat.completions.create(
                    messages=[
                        {"role": "system", "content": system_prompt}, 
                        {"role": "user", "content": user_prompt}
                    ],
                    model = llm_data.model, 
                    temperature = llm_data.temperature
                )         
                output = response.choices[0].message.content
        elif llm_data.api == API.DeepSeek:
            response = clientDeepSeek.chat.completions.create(
                messages=[
                    {"role": "system", "content": system_prompt}, 
                    {"role": "user", "content": user_prompt}
                ],
                model = llm_data.model,
                temperature = llm_data.temperature
            )            
            output = response.choices[0].message.content
        elif llm_data.api == API.Antrophic:
            response = clientAnthropic.messages.create(
                model= llm_data.model,
                max_tokens=10000, #1000
                temperature = llm_data.temperature,
                system=system_prompt,
                messages=[
                    {"role": "user", "content": user_prompt}
                ]
            )
            output = response.content[0].text
        else:
            raise ValueError(f"Unsupported API type: {llm_data.api}")

        end_time_api_call = time.time()
        time_spent_api_call = end_time_api_call - start_time_api_call

    except Exception as e:
        print(f"Error processing {task_id}: {e}")
        log_file.write(f"Error processing {task_id}: {e}\n")
        traceback.print_exc()
        return None, 0
    
    return output, time_spent_api_call

def post_process_llm_output(task_id, output):
    # if first line starts in "Here" remove it
    if output.startswith("Here"):
        output = output[output.find("\n")+1:]

    # Fix problems of misplaced requires/ensures
    output_lines = output.split('\n')

    after_by_method = False

    # do some cleanup
    for i in range(len(output_lines)):
        line = output_lines[i]

        # remove requires/ensures clauses after 'by method'
        if 'by method' in line:
            after_by_method = True
        if after_by_method and '{' in line:
            after_by_method = False  
        if after_by_method and ('requires' in line or 'ensures' in line):
            output_lines[i] = ""
            line = "" 
            if verbose > 1:
                print(f"Removed requires/ensures clause after 'by method' in line {i+1} of file {task_id}: {line}")
            continue

        # remove null checks (not needed in Dafny)
        if 'requires' in line and '!= null' in line:
            output_lines[i] = ""
            line = "" 
            if verbose > 1:
                print(f"Removed null check in line {i+1} of file {task_id}: {line}")
            continue

        # Remove ';' from the end of line of lines that start with requires or ensures
        if (line.strip().startswith('requires ') or line.strip().startswith('ensures ')) and line.strip().endswith(';'):
            output_lines[i] = line[:-1]
            line = output_lines[i]
            if verbose > 1:
                print(f"Removed ';' from end of line in line {i+1} of file {task_id}: {output_lines[i]}")

        # Replace '// Req: '  with 'requires '
        if line.strip().startswith('// Req: '):
            output_lines[i] = line.replace('// Req: ', 'requires ')
            line = output_lines[i]
            if verbose > 1:
                print(f"Replaced '// Req: ' with 'requires ' in line {i+1} of file {task_id}: {output_lines[i]}") 
        
        # Replace '// Ens: '  with 'ensures '
        if line.strip().startswith('// Ens: '):
            output_lines[i] = line.replace('// Ens: ', 'ensures ')
            line = output_lines[i]
            if verbose > 1:
                print(f"Replaced '// Ens: ' with 'ensures ' in line {i+1} of file {task_id}: {output_lines[i]}")

        # Remove ';' from the end of line of lines that start with invariant
        if line.strip().startswith('invariant ') and line.strip().endswith(';'):
            output_lines[i] = line[:-1]
            line = output_lines[i]
            if verbose > 1:
                print(f"Removed ';' from end of line in line {i+1} of file {task_id}: {output_lines[i]}")

        # Remove decreases clause JPF 28OCT2025
        if line.strip().startswith('decreases ') and remove_decreases_clause:
            output_lines[i] = ""
            line = ""
            if verbose > 1:
                print(f"Removed 'decreases' clause in line {i+1} of file {task_id}: {line}")

        # Replace '// Inv: '  with 'invariant '
        if line.strip().startswith('// Inv: '):
            output_lines[i] = line.replace('// Inv: ', 'invariant ')
            line = output_lines[i]
            if verbose > 1:
                print(f"Replaced '// Inv: ' with 'invariant ' in line {i+1} of file {task_id}: {output_lines[i]}")        

        # Replace '[..0..'  with '[..'
        if '[..0..' in line:
            output_lines[i] = line.replace('[..0..', '[..')
            line = output_lines[i]
            if verbose > 1:
                print(f"Replaced '[..0..' with '[..' in line {i+1} of file {task_id}: {output_lines[i]}")

        if line.strip() == "{}": # possibly erased body (removes to facilitate merge!)
            output_lines[i] = ""
            line = ""                   
            if verbose > 1:
                print(f"Removed empty body in line {i+1} of file {task_id}: {line}") 

    # solve problems of misplaced invariants
    saved_invariants = []
    saved_open_brace = []
    expecting_invariant = False
    missing_invariant = False
    for i in range(len(output_lines)):
        line = output_lines[i]
        
        if line.strip().startswith('invariant ') or line.strip().startswith('decreases '):
            if not expecting_invariant: 
                saved_invariants.append(line)
                output_lines[i] = ""
            missing_invariant = False

        elif line.strip().startswith('for ') or line.strip().startswith('while '):
            if saved_open_brace != []:
                output_lines[i] = saved_open_brace[0] + "\n" + line 
                saved_open_brace = []
                line = output_lines[i]
            expecting_invariant = True
            missing_invariant = True
            if saved_invariants != []:
                # insert the saved lines after the current one, keeping the current
                new_line = line 
                # add the saved lines one by one
                for saved_line in saved_invariants:
                    new_line = new_line + "\n" + saved_line 
                saved_invariants = []
                output_lines[i] = new_line
                missing_invariant = False

        elif line.strip() == "{" and missing_invariant:
            saved_open_brace = [line] 
            output_lines[i] = ""

        elif line.strip() != "" and not line.strip().startswith('//'):
            if saved_open_brace != []:
                output_lines[i] = saved_open_brace[0] + "\n" + line 
                saved_open_brace = []
                line = output_lines[i]
            expecting_invariant = False
            missing_invariant = False
            saved_invariants = []

    # Join the lines into a single string separated by newlines
    output = "\n".join(output_lines)

    return output

remove_decreases_clause = True


# Processes a Dafny file using the LLM to generate pre/post conditions
def process_file(filepath, llm_data, trial_number, post_processing = False, repair = False, errors = None, based_on = None):
    
    # Construct the new filename by replacing 'stripped' with 'gpt'
    output_filepath = filepath.replace('_stripped.dfy', f"_{trial_number}_llm.dfy")
    raw_output_filepath = filepath.replace('_stripped.dfy', f"_{trial_number}_llm_raw.dfy")

    if repair:
        file_to_verify = based_on
    else:
        file_to_verify = filepath

    # Read the file content
    with open(file_to_verify, 'r', encoding='utf-8') as file:
        file_content = file.read()

    # select the prompt based on the generation type
    if repair and errors != None:
        instructions_prompt = repair_prompt
    else:
        instructions_prompt = base_prompt

    # Add the file content and errors to the user prompt
    code_prompt = "BEGIN DAFNY\n" + file_content + "\nEND DAFNY\n"
    if repair and errors != None:
        code_prompt += "\nBEGIN VERIFICATION ERRORS\n" + errors + "\nEND VERIFICATION ERRORS\n" 

    # save the prompt to a filename terminating in _prompt.txt
    with open(output_filepath.replace('_llm.dfy', '_prompt.txt'), 'w', encoding='utf-8') as prompt_file:
        prompt_file.write(instructions_prompt + "\n" + code_prompt)
   
    output, time_spent_api_call = call_llm(filepath, llm_data, instructions_prompt, code_prompt)
    
    if output is None or output.strip() == "":
        print(f"Error or empty output when processing {filepath}")
        log_file.write(f"Error or empty output when processing {filepath}\n")
        return None, None, 0

    # Write the API's raw response to the new file
    with open(raw_output_filepath, 'w', encoding='utf-8') as new_raw_file:
        new_raw_file.write(output)

    # extract code between delimiters in output
    if "BEGIN DAFNY\n" in output:
        # extract just the substring between "BEGIN DAFNY" and 'END DAFNY' (excluded)
        output = output[output.find("BEGIN DAFNY") + 12:output.rfind("END DAFNY")]
    elif "```dafny" in output:
        # extract just the substring between "```dafny" and '```' (excluded)
        output = output[output.find("```dafny") + 8:output.rfind("```")]
    elif "```" in output:
        # extract just the substring between "```" and '```' (excluded)
        output = output[output.find("```") + 3:output.rfind("```")]

    # Write the API's response to the new file
    with open(output_filepath, 'w', encoding='utf-8') as new_file:
        new_file.write(output)

    if verbose > 1:
        print(f"LLM output saved to {output_filepath}.")
        log_file.write(f"LLM output saved to {output_filepath}.\n")

    if post_processing:
        post_processed_output = post_process_llm_output(filepath, output)

        # Write the post-processed output
        post_processed_filepath = output_filepath.replace('_llm.dfy', '_merged.dfy')
        with open(post_processed_filepath, 'w', encoding='utf-8') as new_file:
            new_file.write(post_processed_output)

        if verbose > 1:
            print(f"Postprocessed file saved to {post_processed_filepath}")
            log_file.write(f"LLM postprocessed output saved to {post_processed_filepath}\n")
    else:
        post_processed_filepath = None

    return output_filepath, post_processed_filepath, time_spent_api_call

    
# Process all Dany files in the input folder
def process_directory(refined_prompt = True, post_processing = True, repair_mode = False, check_error_type=True, files=None, start_file = None, repair_source = False):
    files_processed = 0 # total number of files processed
    files_verified = 0 # total number of files verified successfully
    total_attempts = 0 # total number of attempts over all files and all LLMs
    original_files_skipped = []
    failed_files = []

    # create CSV file to store the results
    results_file = open(output_folder + r"\_results.csv", "w")
    results_file.write("Filename; Attempt; Success; Time Gen; Time Ver; Time API Call; Success Merged Original; Success Raw; Success Postprocessed\n")

    ignore = True if start_file is not None else False
    
    print(f"Processing folder {input_folder}")
    # loop through the files in the input folder
    for filename in os.listdir(input_folder):
        if ignore:
            if filename == start_file:
                ignore = False
            else:
                continue
        if filename.endswith('.dfy') and (files is None or filename in files):

            filepath = os.path.join(input_folder, filename)
            print(f"\nProcessing {filename}")
            log_file.write(f"Processing {filename}\n")
            succ, initial_verification_errors, initial_num_errors = verify_dafny_file(filepath, False, False)

            if repair_source:
                filename = os.path.basename(filepath)
                new_filename = f"{filename[:-4]}_stripped.dfy"
                new_filepath = os.path.join(output_folder, new_filename)
            else:
                if succ > 1: #!= 1:
                    print(f"{filename}: Original file not verified and skipped")
                    log_file.write(f"{filename}: Original file not verified and skipped\n")
                    original_files_skipped.append(filename)
                    continue

                # create new file with pre/post conditions removed 
                new_filepath = remove_prepostinv_lines_and_save(filepath)
                if new_filepath is None:
                    print(f"{filename}: No pre/post conditions found to remove so this file was skipped")
                    log_file.write(f"{filename}: No pre/post conditions found to remove so this file was skipped\n")
                    original_files_skipped.append(filename)
                    continue

            # try a maximum number of attempts to process the file
            file_verified = False
            file_attempts = 0
            file_successful_attempts = 0

            # loop through the LLMs in the list of llms
            for llm_data in llms:
                if repair_source:
                    verification_errors = initial_verification_errors
                    repairing_file = True
                    last_attempt = filepath 
                    best_attempt = filepath
                    best_num_errors = initial_num_errors
                    best_errors = initial_verification_errors
                else:
                    verification_errors = ""
                    repairing_file = False
                    last_attempt = None
                    best_attempt = None
                    best_num_errors = None
                    best_errors = None
                llm_attempts = 0
                min_attempts = llm_data.min_attempts
                max_independent_attempts = llm_data.max_independent_attempts
                max_attempts = llm_data.max_attempts
                while llm_attempts < min_attempts or (llm_attempts < max_attempts and not file_verified):
                    start_time = time.time()
                    if repair_mode and file_attempts >= max_independent_attempts and verification_errors != "":
                        if repairing_file:
                            llm_output_file, postprocessed_output_file, time3 = process_file(new_filepath, llm_data, file_attempts + 1, repair = True, errors=verification_errors, based_on=last_attempt)
                        else:
                            llm_output_file, postprocessed_output_file, time3 = process_file(new_filepath, llm_data, file_attempts + 1,  repair=True, errors=best_errors, based_on=best_attempt)
                        repairing_file = True    
                    else:
                        llm_output_file, postprocessed_output_file, time3 = process_file(new_filepath, llm_data, file_attempts + 1)
                    end_time = time.time()
                    time_spent = end_time - start_time

                    if llm_output_file == None: # exception
                        continue

                    last_attempt = llm_output_file
                    llm_attempts += 1
                    file_attempts += 1
                    total_attempts += 1

                    start_time2 = time.time()
                    succ_llm_output, verification_errors, num_errors = verify_dafny_file(llm_output_file)
                    end_time2 = time.time()
                    if succ_llm_output != 1 and postprocessed_output_file is not None:
                        succ_postprocessed_output, verification_errors, num_errors = verify_dafny_file(postprocessed_output_file)
                    else:
                        succ_postprocessed_output = succ_llm_output
                        postprocessed_output_file = llm_output_file
                    time_spent2 = end_time2 - start_time2

                    if succ_postprocessed_output == 1:
                        success = 1
                        file_verified = True
                        file_successful_attempts += 1
                        succ_merged_original = 1
                        if verbose > 0:
                            print(f"{filename}: Attempt {file_attempts} successful")
                    else:
                        success = succ_postprocessed_output
                        if best_num_errors == None or num_errors < best_num_errors:
                            best_num_errors = num_errors
                            best_attempt = postprocessed_output_file
                            best_errors = verification_errors                        
                        if verbose > 0:
                            print(f"{filename}: Attempt {file_attempts} failed")
                        if check_error_type:
                            with open(filepath, 'r', encoding='utf-8') as file:
                                original_file_content = file.read()
                            with open(postprocessed_output_file, 'r', encoding='utf-8') as file:
                                generated_file_content = file.read()
                            merged_with_original_content = merge_files(original_file_content, generated_file_content)
                            merged_with_original_path = postprocessed_output_file.replace('_llm.dfy', '_mergedoriginal.dfy')
                            with open(merged_with_original_path, 'w', encoding='utf-8') as new_file:
                                new_file.write(merged_with_original_content)
                            succ_merged_original, _, _ = verify_dafny_file(merged_with_original_path)
                        else:
                            succ_merged_original = 0
        
                    # write the results to the CSV file
                    results_file.write(f"{filename}; {file_attempts}; {success}; {time_spent:.4f}; {time_spent2:.4f}; {time3: .4f}; {succ_merged_original};{succ_llm_output};{succ_postprocessed_output}\n")
                    results_file.flush()

            if file_verified:
                print(f"{filename}: Success")
                log_file.write(f"{filename}: Success\n")
                files_verified += 1
            else:
                print(f"{filename}: Failure")
                log_file.write(f"{filename}: Failure\n")
                failed_files.append(filename)
            files_processed += 1
            if verbose > 0:
                print(f"Processed so far {files_processed} files, {files_verified} verified successfully in {total_attempts} attempts")
            if verbose > 0 and len(original_files_skipped) > 0:
                print(f"Original files not verified and skipped so far: {original_files_skipped}")
            
    print(f"Processed {files_processed} files, {files_verified} verified successfully in {total_attempts} attempts")
    log_file.write(f"Processed {files_processed} files, {files_verified} verified successfully, in {total_attempts} attempts\n")

    if len(failed_files) > 0:
        print(f"Failed files: {failed_files}")
        log_file.write(f"Failed files: {failed_files}\n")

    if len(original_files_skipped) > 0:
        print(f"Original files not verified and skipped: {original_files_skipped}")


process_directory(repair_mode = True, check_error_type = True) 
