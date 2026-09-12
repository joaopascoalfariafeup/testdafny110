"""
Ablation A1, steps 3-4: bounded repair restricted to the test code.

After the test oracles are re-attached (ablation_reattach.py), a program may fail
for two different reasons:

  (a) the generated specification is too weak or incorrect; or
  (b) the specification is adequate, but the verifier needs proof helpers inside
      the test methods that were never generated - in the ablation run the test
      methods were not verified, so the model had no reason to produce them.

This script separates the two. For each failing program it runs a bounded repair
loop in which the model may ONLY add proof helpers inside test methods: the
contracts (requires/ensures), the loop invariants and the auxiliary ghost
declarations are frozen. The restriction is enforced by differencing the
candidate against the program being repaired, not by trusting the prompt.

A program that verifies after this phase was a case of (b): its specification was
strong enough all along. Whatever still fails is a candidate for (a) and goes to
manual classification (step 5).

Comparison conventions follow the minimization procedure of the paper: whitespace
and attributes (e.g. {:fuel 5}) are ignored, so reformatting and verification
hints that carry no logical content are allowed.

Usage:
    python restricted_repair.py <ablation_run_folder> [--max-iterations 3] [--limit N]
"""

import argparse
import csv
import os
import re
import shutil
import sys
from collections import Counter
from pathlib import Path

# ----------------------------------------------------------------- reuse generator

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE))

# generator.py creates its output folder and log at import time; point them at the
# repair output folder before importing.
def _prepare_generator_env(out_folder):
    os.environ["TESTDAFNY_OUTPUT_FOLDER"] = str(out_folder)
    os.environ["TESTDAFNY_DISABLE_TEST_ORACLES"] = "0"


# ------------------------------------------------------------------ test regions

TEST_HEADER = re.compile(
    r"^(\s*)method\s+((?:\{:[^}]*\}\s*)*)([A-Za-z_0-9]+)\s*\(\s*\)(.*)$")

ATTRIBUTE = re.compile(r"\{\s*:[^}]*\}")


def is_test_header(name, rest):
    return (re.search(r"test", name, re.IGNORECASE) is not None or name == "Main") \
           and "returns" not in rest


def find_test_regions(lines):
    """Return a list of (first_line, last_line) index pairs, inclusive, covering
    each test method declaration (header through its closing brace)."""
    regions = []
    i = 0
    while i < len(lines):
        m = TEST_HEADER.match(lines[i].rstrip(chr(13) + chr(10)))
        if m and is_test_header(m.group(3), m.group(4)):
            depth = 0
            started = False
            j = i
            while j < len(lines):
                code = lines[j].split("//")[0]
                for ch in code:
                    if ch == "{":
                        depth += 1
                        started = True
                    elif ch == "}":
                        depth -= 1
                if started and depth <= 0:
                    break
                j += 1
            regions.append((i, min(j, len(lines) - 1)))
            i = j + 1
        else:
            i += 1
    return regions


def split_regions(text):
    """Split source into (outside_test_lines, inside_test_lines)."""
    lines = text.splitlines()
    regions = find_test_regions(lines)
    inside_idx = set()
    for a, b in regions:
        inside_idx.update(range(a, b + 1))
    outside = [l for i, l in enumerate(lines) if i not in inside_idx]
    inside = [l for i, l in enumerate(lines) if i in inside_idx]
    return outside, inside


def normalize(line):
    """Ignore whitespace and attributes, as the minimization procedure does."""
    line = ATTRIBUTE.sub("", line)
    line = re.sub(r"\s+", "", line)
    return line


def meaningful(lines):
    out = []
    for l in lines:
        code = l.split("//")[0]
        n = normalize(code)
        if n:
            out.append(n)
    return out


def check_restriction(original, candidate):
    """Verify the candidate only added helpers inside test methods.

    Returns (ok, reason, details). Two conditions:
      1. the code outside test methods is unchanged (as a multiset of normalized
         lines, so reordering and reformatting are tolerated);
      2. every meaningful line of the original test methods is still present, so
         no test case or assertion was weakened or removed.
    """
    o_out, o_in = split_regions(original)
    c_out, c_in = split_regions(candidate)

    o_out_c, c_out_c = Counter(meaningful(o_out)), Counter(meaningful(c_out))
    added = c_out_c - o_out_c
    removed = o_out_c - c_out_c
    if added or removed:
        details = []
        if added:
            details.append("added outside tests: " + "; ".join(list(added)[:3]))
        if removed:
            details.append("removed outside tests: " + "; ".join(list(removed)[:3]))
        return False, "SPEC_CHANGED", " | ".join(details)

    o_in_c, c_in_c = Counter(meaningful(o_in)), Counter(meaningful(c_in))
    lost = o_in_c - c_in_c
    if lost:
        return False, "TEST_WEAKENED", "removed from tests: " + "; ".join(list(lost)[:3])

    return True, "OK", ""


# --------------------------------------------------------------------------- main

RESTRICTION = """
IMPORTANT ADDITIONAL RESTRICTION FOR THIS TASK:
- Do NOT add, remove or modify any 'requires' or 'ensures' clause.
- Do NOT add, remove or modify any 'invariant' or 'decreases' clause.
- Do NOT add, remove or modify any ghost function, ghost predicate or lemma
  declaration, nor the body of any method under verification.
- The ONLY changes allowed are the addition of proof helpers (assertions, and
  calls to already existing lemmas) INSIDE the bodies of the test methods, and
  the addition of verification hint attributes such as {:fuel n} to existing
  declarations.
- Do NOT remove or weaken any existing test case or test assertion.
The specification is to be treated as fixed; your only task is to help the
verifier discharge the assertions in the test methods.
"""


def extract_code(output):
    if "BEGIN DAFNY\n" in output:
        return output[output.find("BEGIN DAFNY") + 12:output.rfind("END DAFNY")]
    if "```dafny" in output:
        return output[output.find("```dafny") + 8:output.rfind("```")]
    if "```" in output:
        return output[output.find("```") + 3:output.rfind("```")]
    return output


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("folder", help="ablation run folder (must contain _reattach.csv)")
    ap.add_argument("--max-iterations", type=int, default=3)
    ap.add_argument("--limit", type=int, default=None, help="process only the first N programs")
    args = ap.parse_args()

    reattach_csv = os.path.join(args.folder, "_reattach.csv")
    if not os.path.exists(reattach_csv):
        raise SystemExit("Run ablation_reattach.py first: " + reattach_csv + " not found")

    failing = []
    with open(reattach_csv, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            if row["outcome"].endswith("ORACLE_FAIL"):
                # prefer the re-attached artefact written by ablation_reattach.py,
                # which already handles both A1 ({:verify false}) and A2 (sidecar tests)
                rel = row.get("reattached_file") or ""
                path = os.path.join(args.folder, rel) if rel else os.path.join(args.folder, row["file"])
                failing.append((row["program"], path))
    if args.limit:
        failing = failing[:args.limit]

    out_folder = os.path.join(args.folder, "_restricted_repair")
    os.makedirs(out_folder, exist_ok=True)
    _prepare_generator_env(out_folder)

    import generator as g  # noqa: E402  (import after the environment is prepared)

    llm = g.llms[0]
    print(f"Restricted repair of {len(failing)} program(s), model {llm.model}, "
          f"max {args.max_iterations} iteration(s)\n")

    rows = []
    for idx, (program, path) in enumerate(sorted(failing), 1):
        # the file is already re-attached when it comes from _reattached/;
        # the substitution is a no-op in that case and handles A1 files otherwise
        raw = Path(path).read_text(encoding="utf-8", errors="replace")
        original = re.sub(r"\{\s*:verify\s+false\s*\}\s*", "", raw)

        current = original
        work = os.path.join(out_folder, program + "_reattached.dfy")
        Path(work).write_text(current, encoding="utf-8", newline="")

        outcome, iterations, note = "STILL_FAILING", 0, ""
        for it in range(1, args.max_iterations + 1):
            iterations = it
            succ, errors, _ = g.verify_dafny_file(work, False, True)
            if succ == 1:
                outcome = "REPAIRED" if it > 1 else "ALREADY_OK"
                break

            code_prompt = ("BEGIN DAFNY\n" + current + "\nEND DAFNY\n"
                           "\nBEGIN VERIFICATION ERRORS\n" + (errors or "") + "\nEND VERIFICATION ERRORS\n")
            output, _ = g.call_llm(program, llm, g.repair_prompt + RESTRICTION, code_prompt)
            if not output or not output.strip():
                note = "empty LLM output"
                break

            candidate = extract_code(output)
            ok, reason, details = check_restriction(original, candidate)
            if not ok:
                note = f"iteration {it}: {reason} ({details})"
                print(f"  [{idx:3}/{len(failing)}] {program:38} iter {it}: rejected - {reason}")
                continue

            current = candidate
            Path(work).write_text(current, encoding="utf-8", newline="")
        else:
            succ, _, _ = g.verify_dafny_file(work, False, True)
            if succ == 1:
                outcome = "REPAIRED"

        print(f"  [{idx:3}/{len(failing)}] {program:38} {outcome} after {iterations} iteration(s) {note}")
        rows.append(dict(program=program, outcome=outcome, iterations=iterations, note=note,
                         file=os.path.basename(work)))

    out_csv = os.path.join(args.folder, "_restricted_repair.csv")
    with open(out_csv, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["program", "outcome", "iterations", "note", "file"])
        w.writeheader()
        w.writerows(rows)

    counts = Counter(r["outcome"] for r in rows)
    print("\n" + "=" * 62)
    print(f"Programs submitted to restricted repair : {len(rows)}")
    for k, v in sorted(counts.items()):
        print(f"  {k:32} : {v:3}")
    print("=" * 62)
    repaired = counts.get("REPAIRED", 0) + counts.get("ALREADY_OK", 0)
    print(f"\nSpecification was adequate (helpers were missing) : {repaired}")
    print(f"Candidates for genuine under-specification        : {counts.get('STILL_FAILING', 0)}")
    print(f"\nPer-program results written to {out_csv}")


if __name__ == "__main__":
    main()
