# The theory of calendar dates

This Z3 fork extends the solver with a builtin theory of calendar dates
(proleptic Gregorian calendar). The theory is available in the SMT-LIB 2
frontend whenever no standard logic is set (or with `(set-logic ALL)`).

## Signature

| Symbol | Sort | Meaning |
|---|---|---|
| `Date` | sort | a day of the proleptic Gregorian calendar |
| `(date.mk y m d)` | `Int Int Int -> Date` | the date year `y`, month `m`, day `d` |
| `(date.year t)` | `Date -> Int` | year (astronomical numbering: 1 BCE is year 0) |
| `(date.month t)` | `Date -> Int` | month, in `[1, 12]` |
| `(date.day t)` | `Date -> Int` | day of month, in `[1, 31]` |
| `(date.to_days t)` | `Date -> Int` | days since the epoch 1970-01-01 |
| `(date.from_days n)` | `Int -> Date` | inverse of `date.to_days` |
| `(date.add_days t n)` | `Date Int -> Date` | the date `n` days after `t` |
| `(date.sub t1 t2)` | `Date Date -> Int` | days from `t2` to `t1` |
| `(date.dow t)` | `Date -> Int` | ISO-8601 day of week: 1 = Monday ... 7 = Sunday |
| `(date.lt t1 t2)`, `(date.le t1 t2)` | `Date Date -> Bool` | chronological order |
| `(date.valid y m d)` | `Int Int Int -> Bool` | `y-m-d` is a real calendar date |
| `(date.leap_year y)` | `Int -> Bool` | Gregorian leap-year rule |

The calendar is unbounded in both directions (all integer years).
`date.mk` is total; for out-of-range month/day arguments it denotes the date
given by the underlying arithmetic formula (in particular day overflow
carries into the following months: `(date.mk 2026 6 37)` = 2026-07-07).
Use `date.valid` to constrain arguments to real calendar dates.

## Semantics and soundness

The intended structure interprets `Date` as the integers, with `n` denoting
the day `n` days after 1970-01-01; `date.to_days`/`date.from_days` are the
two directions of this bijection and every other operation is defined by a
linear-integer-arithmetic formula over it (Howard Hinnant's `days_from_civil`
and `civil_from_days` algorithms, which are exact for floor-based division —
what SMT-LIB `div`/`mod` by positive constants provide).

Solving reduces the theory to integer arithmetic:

* every date operation is rewritten to its defining arithmetic formula
  (`ast/rewriter/date_rewriter.*`), inside `th_rewriter`, so the reduction
  applies on every solver path (one-shot, incremental, tactic-based);
* equality, `distinct` and `ite` over `Date` are mapped through the
  bijection, which is sound and complete because bijections preserve and
  reflect equality;
* uninterpreted `Date` constants are replaced by `(date.from_days k)` for a
  fresh integer `k` by the `elim-dates` tactic (run at the front of the
  default tactic and of all logic-specific tactics), with a model converter
  that maps models back to `Date` values.

The residual fragment — anything that would let a `Date` term be observed
other than through the bijection, where treating `Date` as an uninterpreted
sort could produce a wrong `sat` — is **rejected with an error** instead:

* uninterpreted functions with `Date` (or a sort containing `Date`) among
  their argument sorts,
* arrays, sequences and datatypes over `Date`,
* quantification (and lambdas) over `Date`.

Uninterpreted *constants* of sort `Date`, and uninterpreted functions
*returning* `Date` from Date-free domains, are fully supported.

On the incremental path (after `push`) the smt core treats `Date` as an
uninterpreted sort, which is sound because every observation of a `Date`
term has already been mapped through `date.to_days` by the rewriter.
`(get-value ...)` evaluates date operations correctly there; `(get-model)`
may display `Date` constants as abstract universe elements (`Date!val!k`)
rather than as `(date.from_days n)` terms.

## Tests

* `*.smt2` — expected results are stated in each file's header comment;
  `run_tests.py` executes all of them and checks the outputs.
* `difftest.py` — differential test of `date.mk`, `date.year/month/day`,
  `date.dow`, `date.valid` against Python's `datetime` on hundreds of random
  dates and day numbers.

```
python3 run_tests.py ../../build/z3
python3 difftest.py ../../build/z3
```
