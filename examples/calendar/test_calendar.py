#!/usr/bin/env python3
"""Test harness for Z3's theory of calendar dates.

Drives the z3 binary (default: ../../build/z3) over SMT-LIB2 input and
checks the calendar operators against two independent references:

  1. Python's datetime module (differential testing on random dates in
     years 1..9999, where datetime is defined).
  2. A naive day-counting reference for years outside datetime's range
     (proleptic Gregorian by explicit month-by-month summation, sharing
     no algorithm with the Hinnant-style expansion used in Z3).

It also checks a set of universal properties by asking the solver to
refute their negations (expecting unsat), and enumerates all models of
a small puzzle (Friday the 13ths of 2025) against Python's calendar.

Exit status 0 iff every check passes.
"""

import calendar
import random
import subprocess
import sys
from datetime import date, timedelta
from pathlib import Path

Z3 = sys.argv[1] if len(sys.argv) > 1 else str(Path(__file__).resolve().parents[2] / "build" / "z3")
EPOCH_ORD = date(1970, 1, 1).toordinal()
random.seed(20260712)

failures = []


def run_z3(script, timeout=600):
    res = subprocess.run([Z3, "-in"], input=script, capture_output=True,
                         text=True, timeout=timeout)
    if res.returncode != 0 or res.stderr.strip():
        raise RuntimeError(f"z3 failed (rc={res.returncode}):\n{res.stderr}\n--- input:\n{script[:2000]}")
    return res.stdout.strip().splitlines()


def lit(n):
    return str(n) if n >= 0 else f"(- {-n})"


def parse_int(line):
    line = line.strip()
    if line.startswith("(-"):
        return -int(line.strip("()- "))
    return int(line)


def check(name, ok, detail=""):
    if ok:
        print(f"  PASS {name}")
    else:
        failures.append(name)
        print(f"  FAIL {name} {detail}")


# ---------------------------------------------------------------------------
# Independent naive reference for the proleptic Gregorian calendar.
# ---------------------------------------------------------------------------

def ref_leap(y):
    return y % 400 == 0 or (y % 4 == 0 and y % 100 != 0)


def ref_days_in_month(y, m):
    if m == 2:
        return 29 if ref_leap(y) else 28
    return 30 if m in (4, 6, 9, 11) else 31


def ref_epoch_naive(y, m, d):
    """Count days between y-m-d and 1970-01-01 one month at a time."""
    days = 0
    yy, mm = 1970, 1
    while (yy, mm) < (y, m):
        days += ref_days_in_month(yy, mm)
        mm += 1
        if mm == 13:
            yy, mm = yy + 1, 1
    while (yy, mm) > (y, m):
        mm -= 1
        if mm == 0:
            yy, mm = yy - 1, 12
        days -= ref_days_in_month(yy, mm)
    return days + (d - 1)


# ---------------------------------------------------------------------------
# 1. Differential test against Python datetime via (simplify ...).
# ---------------------------------------------------------------------------

def diff_test_datetime(n=1500):
    print(f"[1] differential vs datetime on {n} random dates (years 1..9999)")
    dates = []
    for _ in range(n):
        y = random.randint(1, 9999)
        m = random.randint(1, 12)
        d = random.randint(1, ref_days_in_month(y, m))
        dates.append((y, m, d))
    # make sure tricky dates are always included
    dates += [(1970, 1, 1), (2000, 2, 29), (1600, 2, 29), (2400, 2, 29),
              (1, 1, 1), (9999, 12, 31), (1582, 10, 15), (1582, 10, 4),
              (2038, 1, 19), (1900, 3, 1), (2100, 3, 1)]

    lines = []
    for (y, m, d) in dates:
        e = date(y, m, d).toordinal() - EPOCH_ORD
        lines.append(f"(simplify (date.to-epoch {y} {m} {d}))")
        lines.append(f"(simplify (date.year {lit(e)}))")
        lines.append(f"(simplify (date.month {lit(e)}))")
        lines.append(f"(simplify (date.day {lit(e)}))")
        lines.append(f"(simplify (date.day-of-week {lit(e)}))")
        lines.append(f"(simplify (date.days-in-month {y} {m}))")
    out = run_z3("\n".join(lines))
    assert len(out) == 6 * len(dates), f"expected {6*len(dates)} lines, got {len(out)}"

    bad = []
    for i, (y, m, d) in enumerate(dates):
        py = date(y, m, d)
        e = py.toordinal() - EPOCH_ORD
        got = [parse_int(out[6 * i + j]) for j in range(6)]
        want = [e, y, m, d, (py.weekday() + 1) % 7,  # Python: Monday=0; theory: Sunday=0
                ref_days_in_month(y, m)]
        if got != want:
            bad.append((y, m, d, got, want))
    check(f"to-epoch/year/month/day/day-of-week/days-in-month on {len(dates)} dates",
          not bad, f"first mismatch: {bad[:3]}")

    # leap years, differential against calendar.isleap
    years = [random.randint(1, 9999) for _ in range(300)] + [1600, 1700, 1900, 2000, 2100, 2400, 4]
    out = run_z3("\n".join(f"(simplify (date.leap-year {y}))" for y in years))
    bad = [(y, o) for y, o in zip(years, out) if (o.strip() == "true") != calendar.isleap(y)]
    check(f"leap-year on {len(years)} years", not bad, str(bad[:5]))


# ---------------------------------------------------------------------------
# 2. Out-of-datetime-range dates against the naive reference.
# ---------------------------------------------------------------------------

def diff_test_wide_range():
    print("[2] differential vs naive day-counting reference (years -600..12000)")
    dates = [(0, 1, 1), (0, 2, 29), (0, 12, 31), (-1, 12, 31), (-400, 2, 29),
             (-100, 3, 1), (-599, 7, 4), (10000, 1, 1), (12000, 2, 29),
             (-4, 2, 29), (-300, 2, 28)]
    lines = []
    expected = []
    for (y, m, d) in dates:
        e = ref_epoch_naive(y, m, d)
        expected.append((y, m, d, e))
        lines.append(f"(simplify (date.to-epoch {lit(y)} {m} {d}))")
        lines.append(f"(simplify (date.year {lit(e)}))")
        lines.append(f"(simplify (date.month {lit(e)}))")
        lines.append(f"(simplify (date.day {lit(e)}))")
    out = run_z3("\n".join(lines))
    bad = []
    for i, (y, m, d, e) in enumerate(expected):
        got = [parse_int(out[4 * i + j]) for j in range(4)]
        if got != [e, y, m, d]:
            bad.append((y, m, d, got, [e, y, m, d]))
    check(f"proleptic dates incl. year <= 0 on {len(dates)} dates", not bad, str(bad[:3]))

    # weekday continuity across the whole range: naive reference epoch for
    # a far past date, checked against dow formula anchored at 1970.
    out = run_z3("(simplify (date.day-of-week (date.to-epoch (- 44) 3 15)))")
    # 44 BC = year -43 astronomical; year -44 here is just a fixed probe:
    e = ref_epoch_naive(-44, 3, 15)
    check("day-of-week matches mod-7 of naive epoch for year -44",
          parse_int(out[0]) == (e + 4) % 7, f"got {out[0]}")


# ---------------------------------------------------------------------------
# 3. Validity predicate.
# ---------------------------------------------------------------------------

def test_validity():
    print("[3] date.valid on valid/invalid triples")
    valid = [(2000, 2, 29), (2024, 2, 29), (1970, 1, 1), (9999, 12, 31),
             (0, 2, 29), (2026, 7, 12), (1900, 2, 28)]
    invalid = [(1900, 2, 29), (2100, 2, 29), (2026, 2, 29), (2026, 4, 31),
               (2026, 13, 1), (2026, 0, 10), (2026, 6, 0), (2026, 6, -3),
               (2026, 11, 31)]
    lines = [f"(simplify (date.valid {lit(y)} {lit(m)} {lit(d)}))" for (y, m, d) in valid + invalid]
    out = run_z3("\n".join(lines))
    got = [o.strip() == "true" for o in out]
    want = [True] * len(valid) + [False] * len(invalid)
    check("validity verdicts", got == want,
          str([(t, g, w) for t, g, w in zip(valid + invalid, got, want) if g != w]))


# ---------------------------------------------------------------------------
# 4. Full-solver checks: assert disequality with expected value, expect unsat.
# ---------------------------------------------------------------------------

def test_solver_path(n=200):
    print(f"[4] full check-sat path on {n} random dates (expect unsat each)")
    blocks = []
    for _ in range(n):
        y = random.randint(1, 9999)
        m = random.randint(1, 12)
        d = random.randint(1, ref_days_in_month(y, m))
        e = date(y, m, d).toordinal() - EPOCH_ORD
        blocks.append(f"""(push)
(assert (not (and (= (date.to-epoch {y} {m} {d}) {lit(e)})
                  (= (date.year {lit(e)}) {y})
                  (= (date.month {lit(e)}) {m})
                  (= (date.day {lit(e)}) {d}))))
(check-sat)
(pop)""")
    out = run_z3("\n".join(blocks))
    check("all disequalities refuted", all(o == "unsat" for o in out),
          f"statuses: {set(out)}")


# ---------------------------------------------------------------------------
# 5. Universal properties: solver must refute each negation.
# ---------------------------------------------------------------------------

PROPERTIES = [
    ("roundtrip triple->epoch->triple, years 1..9999",
     """(declare-const y Int) (declare-const m Int) (declare-const d Int)
(assert (and (<= 1 y) (<= y 9999) (date.valid y m d)))
(define-fun e () Int (date.to-epoch y m d))
(assert (not (and (= (date.year e) y) (= (date.month e) m) (= (date.day e) d))))"""),
    ("roundtrip epoch->triple->epoch, unbounded epoch",
     """(declare-const e Int)
(assert (not (= (date.to-epoch (date.year e) (date.month e) (date.day e)) e)))"""),
    ("epoch->triple is always a valid date, unbounded epoch",
     """(declare-const e Int)
(assert (not (date.valid (date.year e) (date.month e) (date.day e))))"""),
    ("month of any epoch day lies in [1,12], unbounded",
     """(declare-const e Int)
(assert (or (< (date.month e) 1) (> (date.month e) 12)))"""),
    ("day of any epoch day lies in [1,31], unbounded",
     """(declare-const e Int)
(assert (or (< (date.day e) 1) (> (date.day e) 31)))"""),
    ("day-of-week lies in [0,6] and increments mod 7, unbounded",
     """(declare-const e Int)
(assert (or (< (date.day-of-week e) 0) (> (date.day-of-week e) 6)
            (not (= (date.day-of-week (+ e 1)) (mod (+ (date.day-of-week e) 1) 7)))))"""),
    ("400-year cycle: to-epoch shifts by exactly 146097 days, unbounded year",
     """(declare-const y Int) (declare-const m Int) (declare-const d Int)
(assert (date.valid y m d))
(assert (not (= (date.to-epoch (+ y 400) m d) (+ (date.to-epoch y m d) 146097))))"""),
    ("leap-year has period 400, unbounded",
     """(declare-const y Int)
(assert (not (= (date.leap-year y) (date.leap-year (+ y 400)))))"""),
    ("Feb 29 valid iff leap year, unbounded",
     """(declare-const y Int)
(assert (not (= (date.valid y 2 29) (date.leap-year y))))"""),
    ("successor day within a month has successor epoch, unbounded",
     """(declare-const y Int) (declare-const m Int) (declare-const d Int)
(assert (and (date.valid y m d) (date.valid y m (+ d 1))))
(assert (not (= (date.to-epoch y m (+ d 1)) (+ (date.to-epoch y m d) 1))))"""),
    ("strict monotonicity in lexicographic date order, years 1900..2200",
     """(declare-const y1 Int) (declare-const m1 Int) (declare-const d1 Int)
(declare-const y2 Int) (declare-const m2 Int) (declare-const d2 Int)
(assert (and (<= 1900 y1) (<= y1 2200) (<= 1900 y2) (<= y2 2200)))
(assert (and (date.valid y1 m1 d1) (date.valid y2 m2 d2)))
(assert (or (< y1 y2) (and (= y1 y2) (< m1 m2)) (and (= y1 y2) (= m1 m2) (< d1 d2))))
(assert (not (< (date.to-epoch y1 m1 d1) (date.to-epoch y2 m2 d2))))"""),
    ("a year contains 365 or 366 days, unbounded",
     """(declare-const y Int)
(define-fun len () Int (- (date.to-epoch (+ y 1) 1 1) (date.to-epoch y 1 1)))
(assert (not (= len (ite (date.leap-year y) 366 365))))"""),
]


def test_properties():
    print(f"[5] universal properties ({len(PROPERTIES)} unsat queries)")
    for name, body in PROPERTIES:
        out = run_z3(body + "\n(check-sat)\n", timeout=600)
        check(name, out[-1] == "unsat", f"got {out[-1]}")


# ---------------------------------------------------------------------------
# 6. Model enumeration puzzle: all Friday the 13ths of 2025.
# ---------------------------------------------------------------------------

def test_friday_13():
    print("[6] enumerate Friday the 13ths of 2025")
    script = """(declare-const e Int)
(assert (and (= (date.year e) 2025) (= (date.day e) 13) (= (date.day-of-week e) 5)))
"""
    found = []
    for _ in range(15):
        base = script + "".join(f"(assert (distinct e {lit(v)}))\n" for v in found)
        if run_z3(base + "(check-sat)\n")[0] == "unsat":
            break
        out = run_z3(base + "(check-sat)\n(get-value (e))\n")
        assert out[0] == "sat", out
        v = parse_int(out[1].replace("((e", "").replace("))", ""))
        found.append(v)
    else:
        check("enumeration terminated", False, "more than 15 models?!")
        return
    got = sorted(date(1970, 1, 1) + timedelta(days=v) for v in found)
    want = [date(2025, m, 13) for m in range(1, 13)
            if date(2025, m, 13).weekday() == 4]
    check(f"found {[d.isoformat() for d in got]}", got == want, f"want {want}")


# ---------------------------------------------------------------------------
# 7. Sanity: the extension does not disturb ordinary solving.
# ---------------------------------------------------------------------------

def test_sanity():
    print("[7] sanity of ordinary solving")
    out = run_z3("""(declare-const x Int) (declare-const y Int)
(assert (and (< x y) (< y (+ x 2))))
(check-sat)
(reset)
(declare-const p Bool)
(assert (and p (not p)))
(check-sat)
(reset)
(declare-fun date.mine (Int) Int)   ; user symbols with a date. prefix still work
(assert (= (date.mine 3) 4))
(check-sat)
""")
    check("plain queries unaffected", out == ["sat", "unsat", "sat"], str(out))


if __name__ == "__main__":
    print(f"z3 binary: {Z3}")
    diff_test_datetime()
    diff_test_wide_range()
    test_validity()
    test_solver_path()
    test_properties()
    test_friday_13()
    test_sanity()
    print()
    if failures:
        print(f"{len(failures)} FAILED: {failures}")
        sys.exit(1)
    print("all calendar theory tests passed")
