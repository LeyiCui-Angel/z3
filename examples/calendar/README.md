# Theory of calendar dates

This directory documents and tests Z3's theory of calendar dates: a family
of interpreted functions over the integers for reasoning about dates in the
**proleptic Gregorian calendar** (the Gregorian leap-year rules extended
indefinitely in both directions, with astronomical year numbering, so year 0
exists and is a leap year).

A date is represented either by a `(year, month, day)` triple of integers or
by its **epoch day number**: the number of days elapsed since 1970-01-01
(negative for earlier days).

## Operators

| Operator | Signature | Meaning |
|---|---|---|
| `(date.to-epoch y m d)` | `Int Int Int -> Int` | epoch day number of the date `y-m-d` |
| `(date.year e)` | `Int -> Int` | year of epoch day `e` |
| `(date.month e)` | `Int -> Int` | month (1..12) of epoch day `e` |
| `(date.day e)` | `Int -> Int` | day of month (1..31) of epoch day `e` |
| `(date.day-of-week e)` | `Int -> Int` | 0 = Sunday, ..., 6 = Saturday |
| `(date.leap-year y)` | `Int -> Bool` | Gregorian leap-year predicate |
| `(date.days-in-month y m)` | `Int Int -> Int` | days in month `m` of year `y` |
| `(date.valid y m d)` | `Int Int Int -> Bool` | `1 <= m <= 12` and `1 <= d <= days-in-month(y, m)` |

`date.year`/`date.month`/`date.day` decode any integer `e` to the unique
valid date with that epoch number, so
`(date.to-epoch (date.year e) (date.month e) (date.day e)) = e` holds for
all integers `e`.  `date.to-epoch` is total; on triples that are not valid
dates it is pinned down by its defining arithmetic expression (in
particular it is linear in `d`, so e.g. `(date.to-epoch 2026 1 32)`
equals `(date.to-epoch 2026 2 1)`).

The operators are available when no logic is set and under `(set-logic ALL)`;
standard SMT-LIB logics such as `QF_LIA` do not include them.

## Soundness

The theory is implemented as a *definitional extension*.  Every operator is
eliminated during rewriting (`src/ast/rewriter/calendar_rewriter.cpp`) by
macro-expanding it into an equivalent term of linear integer arithmetic:
integer division and modulus by positive numeric constants plus
if-then-else, following Howard Hinnant's `days_from_civil` /
`civil_from_days` algorithms restated over SMT-LIB semantics (for a
positive constant `n`, `(div x n)` is `floor(x/n)` and `(mod x n)` lies in
`[0, n-1]` for *every* integer `x`, which makes the era decomposition total
without case splits on signs).  The expansion introduces no fresh symbols,
no axioms, and no side conditions, so it preserves satisfiability, validity
and models exactly; the core solvers are untouched and every solver
frontend (SMT kernel, tactics, model evaluation) sees only plain arithmetic.

Correctness of the expansion itself is checked by the tests below against
two independent references.

## Tests

* `test_calendar.py` — end-to-end harness driving the `z3` binary:
  differential testing against Python's `datetime` on random dates
  (years 1..9999), against a naive month-by-month day-counting reference
  outside `datetime`'s range (years -600..12000), validity tables,
  full `check-sat`-path checks, twelve universal properties proved unsat
  (round trips, bounds, the 146097-day/400-year cycle, monotonicity,
  year lengths), model enumeration of the Friday-the-13ths of 2025, and
  sanity checks that ordinary solving is unaffected.

  ```bash
  python3 examples/calendar/test_calendar.py [path/to/z3]
  ```

* `src/test/calendar.cpp` — C++ unit test (`test-z3 calendar`) comparing
  the rewriter against the naive reference on 4000 random dates in years
  -1000..3000.

* `calendar_example.smt2` — a small showcase:

  ```bash
  z3 examples/calendar/calendar_example.smt2
  ```
