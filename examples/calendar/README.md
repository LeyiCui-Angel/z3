# Theory of calendar dates

Z3 supports a small theory of calendar dates over the **proleptic Gregorian
calendar**.  All operators work on integers; a date is given either by its
fields `(year, month, day)` or by its **epoch day number** — the number of
days since 1970-01-01 (day 0).  Years use astronomical numbering (year 0 =
1 BC, year -1 = 2 BC, ...), and the Gregorian leap rules are extrapolated to
all integers.

## Operators

| Operator | Signature | Meaning |
|---|---|---|
| `date.is-leap-year`  | `Int -> Bool`         | Gregorian leap-year test |
| `date.days-in-month` | `Int Int -> Int`      | days in month `m` of year `y`; `0` if `m` is not in `[1, 12]` |
| `date.valid`         | `Int Int Int -> Bool` | `(y, m, d)` is a calendar date |
| `date.to-epoch`      | `Int Int Int -> Int`  | epoch day number of `(y, m, d)` |
| `date.year`          | `Int -> Int`          | year of epoch day `n` |
| `date.month`         | `Int -> Int`          | month of epoch day `n`, in `[1, 12]` |
| `date.day`           | `Int -> Int`          | day-of-month of epoch day `n`, in `[1, 31]` |
| `date.day-of-week`   | `Int -> Int`          | day of week of epoch day `n`, in `[0, 6]`, `0` = Sunday |

The operators are available in the default logic and under `(set-logic ALL)`.

## Example

```smt2
; in which months of 2026 does Friday the 13th fall?
(declare-const m Int)
(assert (date.valid 2026 m 13))
(assert (= (date.day-of-week (date.to-epoch 2026 m 13)) 5))
(check-sat)
(get-model)
```

## Semantics and soundness

Every operator is *defined* by a total expansion into integer arithmetic
(addition, multiplication by constants, `div`/`mod` by positive numeric
constants, `ite`, boolean connectives), implemented in
`src/ast/rewriter/calendar_rewriter.cpp` and applied by `th_rewriter` during
preprocessing.  The field/epoch conversions use Howard Hinnant's
`days_from_civil` / `civil_from_days` algorithms, which are exact on the
proleptic Gregorian calendar for all integer years.

Because the expansion introduces no fresh symbols, it is definitional: the
extension is conservative, sound in any polarity and under quantifiers, and
lands in a decidable fragment (linear integer arithmetic with `div`/`mod` by
constants), so it is complete as well.  On invalid field triples
`date.to-epoch` still denotes the total function computed by the expansion;
use `date.valid` to constrain to real dates.

If preprocessing is disabled (`smt.preprocess=false`), the smt core rejects
formulas containing calendar operators instead of unsoundly treating them as
uninterpreted functions.

## Tests

```bash
cd examples/calendar
python3 run_tests.py --z3 ../../build/z3
```

The harness checks, among other things:

* thousands of ground evaluations against Python's `datetime` module
  (years 1..9999) and a reference implementation (all years),
* solver-level proofs of round-trip identities (`date.to-epoch` after
  `date.year`/`date.month`/`date.day` is the identity and vice versa),
  monotonicity of `date.to-epoch` w.r.t. lexicographic field order, field
  range invariants, and leap-cycle periodicity (`calendar_props.smt2`),
* model extraction and `(eval ...)` on satisfiable date constraints,
* the `smt.preprocess=false` soundness guard.
