#!/usr/bin/env python3
"""Differential test for the Z3 calendar date theory.

Cross-checks the theory against Python's datetime module (an independent
implementation of the proleptic Gregorian calendar):

  1. date.to_days / date.dow of random valid dates match datetime.
  2. date.year/month/day of random day numbers match datetime.
  3. date.valid matches datetime's constructor on random (y, m, d) triples,
     including invalid ones.

Each batch is emitted as the negation of a big conjunction, so z3 must answer
"unsat" on facts and the script also includes a satisfiable control to guard
against a solver that answers unsat for trivial reasons.

Usage: python3 difftest.py [path-to-z3] [num-samples]
"""
import random
import subprocess
import sys
from datetime import date, timedelta

Z3 = sys.argv[1] if len(sys.argv) > 1 else "z3"
N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
EPOCH = date(1970, 1, 1).toordinal()

random.seed(20260707)


def run(smt: str) -> list[str]:
    p = subprocess.run([Z3, "-in"], input=smt, capture_output=True, text=True, timeout=600)
    out = (p.stdout + p.stderr).strip()
    return out.splitlines()


def batch_facts(facts: list[str]) -> None:
    smt = "(assert (not (and\n  " + "\n  ".join(facts) + ")))\n(check-sat)\n"
    lines = run(smt)
    assert lines == ["unsat"], f"expected unsat, got {lines}"


def main() -> None:
    facts_to_days = []
    facts_from_days = []
    facts_valid = []

    # 1. random valid dates: to_days and dow
    for _ in range(N):
        o = random.randint(1, date(9999, 12, 31).toordinal())
        dt = date.fromordinal(o)
        z = o - EPOCH
        zs = str(z) if z >= 0 else f"(- {-z})"
        facts_to_days.append(f"(= (date.to_days (date.mk {dt.year} {dt.month} {dt.day})) {zs})")
        facts_to_days.append(f"(= (date.dow (date.mk {dt.year} {dt.month} {dt.day})) {dt.isoweekday()})")

    # 2. random day numbers: year/month/day
    for _ in range(N):
        o = random.randint(1, date(9999, 12, 31).toordinal())
        dt = date.fromordinal(o)
        z = o - EPOCH
        zs = str(z) if z >= 0 else f"(- {-z})"
        facts_from_days.append(f"(= (date.year  (date.from_days {zs})) {dt.year})")
        facts_from_days.append(f"(= (date.month (date.from_days {zs})) {dt.month})")
        facts_from_days.append(f"(= (date.day   (date.from_days {zs})) {dt.day})")

    # 3. random (y, m, d) triples vs. datetime's validity check
    for _ in range(N):
        y = random.randint(1, 9999)
        m = random.randint(-1, 14)
        d = random.randint(-1, 33)
        try:
            date(y, m, d)
            ok = True
        except ValueError:
            ok = False
        lit = f"(date.valid {y} {m} {d})"
        facts_valid.append(lit if ok else f"(not {lit})")

    batch_facts(facts_to_days)
    print(f"to_days/dow: {N} random dates ok")
    batch_facts(facts_from_days)
    print(f"year/month/day: {N} random day numbers ok")
    batch_facts(facts_valid)
    print(f"valid: {N} random triples ok")

    # satisfiable control: make sure unsat is not vacuous
    lines = run("(declare-const d Date)\n(assert (= (date.year d) 2026))\n(check-sat)\n")
    assert lines == ["sat"], f"control: expected sat, got {lines}"
    print("sat control ok")
    print("ALL DIFFERENTIAL TESTS PASSED")


if __name__ == "__main__":
    main()
