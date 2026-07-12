#!/usr/bin/env python3
"""Test harness for Z3's calendar-date theory (proleptic Gregorian calendar).

Runs four groups of tests against a z3 binary:

1. differential: evaluate ground calendar terms with (simplify ...) and
   compare against Python's datetime module (the external ground truth,
   years 1..9999) and against an independent reference implementation of
   the civil-date algorithms (validated against datetime on the common
   range) for years outside datetime's range.
2. properties:   run calendar_props.smt2; every negated valid statement
   must come back unsat, and the sat sanity checks must come back sat.
3. models:       satisfiable queries; extracted models are cross-checked
   in Python.  Also exercises (eval ...) through the model evaluator.
4. guard:        with preprocessing disabled the smt core must reject
   calendar operators with an error instead of silently treating them
   as uninterpreted functions (which would be unsound).

Usage: python3 run_tests.py [--z3 PATH] [--samples N] [--seed N]
"""

import argparse
import random
import subprocess
import sys
from datetime import date

EPOCH_ORD = date(1970, 1, 1).toordinal()

# ---------------------------------------------------------------------------
# reference implementation (all-integer-years; Python's // and % are floor
# division, which matches SMT-LIB Euclidean div/mod for positive divisors)
# ---------------------------------------------------------------------------

def ref_is_leap(y):
    return (y % 4 == 0 and y % 100 != 0) or y % 400 == 0

def ref_days_in_month(y, m):
    if m in (1, 3, 5, 7, 8, 10, 12):
        return 31
    if m in (4, 6, 9, 11):
        return 30
    if m == 2:
        return 29 if ref_is_leap(y) else 28
    return 0

def ref_valid(y, m, d):
    return 1 <= m <= 12 and 1 <= d <= ref_days_in_month(y, m)

def ref_to_epoch(y, m, d):
    yy = y - 1 if m <= 2 else y
    era = yy // 400
    yoe = yy - era * 400
    mp = (m + 9) % 12
    doy = (153 * mp + 2) // 5 + d - 1
    doe = yoe * 365 + yoe // 4 - yoe // 100 + doy
    return era * 146097 + doe - 719468

def ref_from_epoch(n):
    z = n + 719468
    era = z // 146097
    doe = z - era * 146097
    yoe = (doe - doe // 1460 + doe // 36524 - doe // 146096) // 365
    y = yoe + era * 400
    doy = doe - (365 * yoe + yoe // 4 - yoe // 100)
    mp = (5 * doy + 2) // 153
    d = doy - (153 * mp + 2) // 5 + 1
    m = mp + 3 if mp < 10 else mp - 9
    return (y + 1 if m <= 2 else y, m, d)

def ref_dow(n):
    # 0 = Sunday, ..., 6 = Saturday; day 0 (1970-01-01) was a Thursday
    return (n + 4) % 7

def dt_to_epoch(y, m, d):
    return date(y, m, d).toordinal() - EPOCH_ORD

# ---------------------------------------------------------------------------
# z3 driving
# ---------------------------------------------------------------------------

def run_z3(z3, script, extra_args=(), timeout=600):
    p = subprocess.run([z3, *extra_args, "-in"], input=script,
                       capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout, p.stderr

def parse_values(out):
    """Parse one simplify result per line: integers (possibly (- n)) or booleans."""
    vals = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        if line == "true":
            vals.append(True)
        elif line == "false":
            vals.append(False)
        elif line.startswith("(-"):
            vals.append(-int(line[2:-1].strip()))
        else:
            vals.append(int(line))
    return vals

# ---------------------------------------------------------------------------
# test groups
# ---------------------------------------------------------------------------

def gen_dates(samples, rng):
    """(y, m, d) triples: valid and invalid, in and out of datetime's range."""
    cases = [
        (1970, 1, 1), (1969, 12, 31), (2000, 2, 29), (1900, 2, 28), (1900, 2, 29),
        (1900, 3, 1), (2000, 12, 31), (1, 1, 1), (0, 1, 1), (0, 2, 29), (0, 12, 31),
        (-1, 12, 31), (400, 2, 29), (-400, 2, 29), (-401, 2, 29), (9999, 12, 31),
        (1582, 10, 15), (2026, 7, 12), (2024, 2, 29), (2100, 2, 28), (2100, 2, 29),
        (2026, 0, 10), (2026, 13, 1), (2026, 6, 31), (2026, 4, 0), (2026, 2, 30),
        (-9999, 1, 1), (100000, 6, 15), (-100000, 6, 15),
    ]
    for _ in range(samples):
        y = rng.randint(1, 9999)
        m = rng.randint(1, 12)
        d = rng.randint(1, ref_days_in_month(y, m))
        cases.append((y, m, d))
    for _ in range(samples // 4):
        cases.append((rng.randint(-100000, 100000), rng.randint(-5, 20), rng.randint(-5, 40)))
    return cases

def test_differential(z3, samples, rng):
    # sanity: the reference implementation must agree with datetime
    for _ in range(samples):
        y = rng.randint(1, 9999)
        m = rng.randint(1, 12)
        d = rng.randint(1, ref_days_in_month(y, m))
        n = dt_to_epoch(y, m, d)
        assert ref_to_epoch(y, m, d) == n, (y, m, d)
        assert ref_from_epoch(n) == (y, m, d), n
        assert ref_dow(n) == (date(y, m, d).weekday() + 1) % 7, (y, m, d)

    cases = gen_dates(samples, rng)
    epochs = sorted({ref_to_epoch(y, m, d) for (y, m, d) in cases if ref_valid(y, m, d)}
                    | {0, -1, 1, -719468, -719469, 146096, -146097,
                       rng.randint(-4_000_000, 4_000_000)})

    lines = []
    expected = []
    def lit(v):
        return str(v) if v >= 0 else "(- {})".format(-v)
    for (y, m, d) in cases:
        lines.append("(simplify (date.is-leap-year {}))".format(lit(y)))
        expected.append(ref_is_leap(y))
        lines.append("(simplify (date.days-in-month {} {}))".format(lit(y), lit(m)))
        expected.append(ref_days_in_month(y, m))
        lines.append("(simplify (date.valid {} {} {}))".format(lit(y), lit(m), lit(d)))
        expected.append(ref_valid(y, m, d))
        lines.append("(simplify (date.to-epoch {} {} {}))".format(lit(y), lit(m), lit(d)))
        expected.append(ref_to_epoch(y, m, d))
    for n in epochs:
        yy, mm, dd = ref_from_epoch(n)
        for op, val in (("date.year", yy), ("date.month", mm), ("date.day", dd),
                        ("date.day-of-week", ref_dow(n))):
            lines.append("(simplify ({} {}))".format(op, lit(n)))
            expected.append(val)

    rc, out, err = run_z3(z3, "\n".join(lines))
    if rc != 0 or err.strip():
        print("z3 failed on differential script:", rc, err)
        return 1
    got = parse_values(out)
    if len(got) != len(expected):
        print("differential: expected {} results, got {}".format(len(expected), len(got)))
        return 1
    bad = 0
    for i, (g, e) in enumerate(zip(got, expected)):
        if g != e:
            print("differential mismatch: {}  ->  {}  (expected {})".format(lines[i], g, e))
            bad += 1
    print("differential: {} ground evaluations checked, {} mismatches".format(len(expected), bad))
    return 1 if bad else 0

def test_properties(z3, props_file):
    p = subprocess.run([z3, props_file], capture_output=True, text=True, timeout=1200)
    if p.returncode != 0 or p.stderr.strip():
        print("z3 failed on", props_file, p.returncode, p.stderr)
        return 1
    results = {}
    label = None
    for line in p.stdout.splitlines():
        line = line.strip()
        if line in ("sat", "unsat", "unknown"):
            results[label] = line
        elif line:
            label = line
    bad = 0
    for label, res in results.items():
        want = "sat" if label.startswith("sat-sanity") else "unsat"
        status = "ok" if res == want else "FAIL"
        if res != want:
            bad += 1
        print("property {:20s} {:8s} ({})".format(label, res, status))
    return 1 if bad else 0

def test_models(z3, rng):
    bad = 0

    # find all Friday-the-13th months of 2026, one model at a time
    fridays = {m for m in range(1, 13) if date(2026, m, 13).weekday() == 4}
    found = set()
    excluded = ""
    for _ in range(13):
        script = """
(declare-const m Int)
(assert (date.valid 2026 m 13))
(assert (= (date.day-of-week (date.to-epoch 2026 m 13)) 5))
{}
(check-sat)
(get-value (m))
""".format(excluded)
        rc, out, err = run_z3(z3, script)
        if "unsat" in out:
            break
        try:
            mv = int(out.split("(m")[1].split(")")[0].strip())
        except (IndexError, ValueError):
            print("models: could not parse Friday-13th response:", out, err)
            return 1
        found.add(mv)
        excluded += "(assert (distinct m {}))\n".format(" ".join(str(v) for v in sorted(found)))
    if found != fridays:
        print("models: Friday-the-13th months of 2026: got {}, expected {}".format(
            sorted(found), sorted(fridays)))
        bad += 1
    else:
        print("models: Friday-the-13th months of 2026 = {} (ok)".format(sorted(found)))

    # invert the epoch function on a random day; also exercises (eval ...)
    n = rng.randint(-1_000_000, 1_000_000)
    yy, mm, dd = ref_from_epoch(n)
    script = """
(declare-const y Int)
(declare-const m Int)
(declare-const d Int)
(assert (date.valid y m d))
(assert (= (date.to-epoch y m d) {}))
(check-sat)
(get-value (y m d))
(eval (date.year {}))
(eval (date.day-of-week {}))
""".format(n, n, n)
    rc, out, err = run_z3(z3, script)
    ok = ("sat" in out
          and "(y {})".format(yy if yy >= 0 else "(- {})".format(-yy)) in out.replace("\n", " ")
          and "(m {})".format(mm) in out
          and "(d {})".format(dd) in out)
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    ok = ok and lines[-2:] == [str(yy) if yy >= 0 else "(- {})".format(-yy), str(ref_dow(n))]
    if not ok:
        print("models: epoch inversion for n={} failed:\n{}{}".format(n, out, err))
        bad += 1
    else:
        print("models: epoch {} inverted to {:05d}-{:02d}-{:02d} and eval agrees (ok)".format(n, yy, mm, dd))
    return 1 if bad else 0

def test_guard(z3):
    script = """
(declare-const n Int)
(assert (= (date.day-of-week n) 6))
(check-sat)
"""
    rc, out, err = run_z3(z3, script, extra_args=("smt.preprocess=false",))
    combined = out + err
    if "error" in combined and "calendar operators" in combined:
        print("guard: smt.preprocess=false is rejected with an error (ok)")
        return 0
    # answering sat here happens to be correct, but only by accident; the
    # guard must prevent the core from ever treating the ops as uninterpreted
    print("guard: expected an error, got:\n", combined)
    return 1

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--z3", default="../../build/z3")
    ap.add_argument("--samples", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--props", default="calendar_props.smt2")
    args = ap.parse_args()
    rng = random.Random(args.seed)

    failures = 0
    failures += test_differential(args.z3, args.samples, rng)
    failures += test_properties(args.z3, args.props)
    failures += test_models(args.z3, rng)
    failures += test_guard(args.z3)
    print("=" * 60)
    print("ALL TESTS PASSED" if failures == 0 else "{} TEST GROUP(S) FAILED".format(failures))
    return failures

if __name__ == "__main__":
    sys.exit(main())
