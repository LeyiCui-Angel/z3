#!/usr/bin/env python3
"""Run the .smt2 tests in this directory and check their outputs.

Usage: python3 run_tests.py [path-to-z3]
"""
import subprocess
import sys
from pathlib import Path

Z3 = sys.argv[1] if len(sys.argv) > 1 else "z3"
HERE = Path(__file__).parent

# expected complete stdout+stderr, one entry per line; "ERROR" matches any
# line starting with (error
EXPECTED = {
    "known_facts.smt2": ["unsat"],
    "ordering.smt2": ["unsat"],
    "add_days.smt2": ["unsat"],
    "injectivity.smt2": ["unsat"],
    "solve_model.smt2": ["sat", "(((date.day d) 7)", " ((date.to_days d) 20641))"],
    "century_leap.smt2": ["sat", "((y 2000))", "unsat"],
    "symbolic_ymd.smt2": ["sat", "((y 2026)", " (m 7)", " (d 7))", "unsat"],
    "incremental.smt2": ["sat", "unsat", "sat", "unsat", "sat",
                         "(((date.year e) 2027)", " ((date.month e) 7)", " ((date.day e) 7))"],
    "unsupported_uf.smt2": ["ERROR"],
    "unsupported_quant.smt2": ["ERROR"],
    "unsupported_array.smt2": ["ERROR"],
}

def main() -> None:
    failures = 0
    for name, expected in EXPECTED.items():
        p = subprocess.run([Z3, str(HERE / name)], capture_output=True, text=True, timeout=600)
        lines = (p.stdout + p.stderr).strip().splitlines()
        ok = True
        if expected == ["ERROR"]:
            ok = len(lines) >= 1 and all(l.startswith("(error") for l in lines) \
                 and not any(l in ("sat", "unsat") for l in lines)
        else:
            ok = lines == expected
        status = "PASS" if ok else "FAIL"
        if not ok:
            failures += 1
            print(f"{status} {name}\n  expected: {expected}\n  got:      {lines}")
        else:
            print(f"{status} {name}")
    if failures:
        print(f"{failures} test(s) failed")
        sys.exit(1)
    print("ALL TESTS PASSED")

if __name__ == "__main__":
    main()
