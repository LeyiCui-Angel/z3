# The Date theory

This Z3 checkout extends the solver with the native theory of calendar
dates specified in `Dates.smt2`: sort `Date`, constructor `date.mk`,
selectors `date.year`/`date.month`/`date.day`, arithmetic
`date.add`/`date.sub`, and comparisons `date.lt`/`date.le`/`date.gt`/
`date.ge`. Equality and `distinct` are the built-in Core operators.

The theory is available with no `set-logic` command or with
`(set-logic ALL)`.

## Semantic decisions

`Dates.smt2` specifies syntax only, so the following interpretation was
chosen and implemented uniformly across the rewriter and both solver
pipelines. The guiding principles: use the conventions mainstream
calendar libraries agree on, make every operation total, and keep the
theory decidable by reduction to linear integer arithmetic.

1. **Domain.** `Date` denotes the days of the proleptic Gregorian
   calendar, extended without bounds in both directions. Years use
   astronomical numbering: year 0 exists (and is a leap year), year -1
   precedes it. The domain is countably infinite and in bijection with
   the integers by counting days from an epoch; day 0 is 1970-01-01.
   The bijection is Howard Hinnant's `days_from_civil`/`civil_from_days`
   construction, whose only nonlinear operations are integer divisions
   by positive constants — hence every date constraint reduces to
   linear integer arithmetic with `div`/`mod` by constants, which Z3's
   arithmetic solvers decide.

2. **`(date.mk y m d)` is total and normalizing** (mktime/JavaScript
   `Date` convention). First the month is normalized into the year:
   `y' = y + floor((m-1)/12)`, `m' = ((m-1) mod 12) + 1`; then the
   result is the day `d - 1` days after the first day of month
   `(y', m')`. Consequently out-of-range months and days roll over
   rather than being rejected, e.g.

   | term | value |
   |---|---|
   | `(date.mk 2000 2 30)` | 2000-03-01 (Feb 2000 has 29 days) |
   | `(date.mk 2021 13 1)` | 2022-01-01 |
   | `(date.mk 2020 1 0)`  | 2019-12-31 |
   | `(date.mk 2020 -1 15)`| 2019-11-15 |
   | `(date.mk 1900 2 29)` | 1900-03-01 (1900 is not a leap year) |

   Rationale: the task requires `date.mk` to be well-sorted on all
   integer arguments, so a semantic decision is needed for out-of-range
   triples. Rolling over (rather than clamping or mapping to an error
   value) is the standard totalization used by C `mktime` and
   JavaScript, keeps `date.mk` surjective, and gives clean algebraic
   laws such as `(date.mk y m (+ d k))` = `(date.mk y m d)` plus `k`
   days.

3. **Selectors return the normalized components.** For every date
   value `v`: `1 <= (date.month v) <= 12`,
   `1 <= (date.day v) <= days-in-month(year v, month v)`, and the
   round-trip identity
   `(date.mk (date.year v) (date.month v) (date.day v)) = v` holds.

4. **`(date.add d py pm pd)`: month arithmetic clamps, day arithmetic
   is exact** (java.time / .NET / python-dateutil convention). The
   offsets are applied as: add `12*py + pm` months to the (year, month)
   pair of `d`; clamp the day-of-month of `d` to the length of the
   resulting month; then add `pd` days exactly.

   | term | value |
   |---|---|
   | `(date.add (date.mk 2020 1 31) 0 1 0)` | 2020-02-29 (clamped) |
   | `(date.add (date.mk 2019 1 31) 0 1 0)` | 2019-02-28 (clamped) |
   | `(date.add (date.mk 2020 2 29) 1 0 0)` | 2021-02-28 (clamped) |
   | `(date.add (date.mk 2020 1 31) 0 0 1)` | 2020-02-01 |

   Rationale: this is the dominant convention for "add N months" in
   calendar libraries (`java.time.LocalDate.plusMonths`, .NET
   `DateTime.AddMonths`, `dateutil.relativedelta`), matching the
   intuition that "one month after Jan 31" is the end of February.
   Year and month offsets are combined into a single month shift
   before clamping, exactly as `relativedelta(years=py, months=pm)`
   does. Day offsets are exact day counts and never clamp.

5. **`(date.sub d py pm pd) = (date.add d (- py) (- pm) (- pd))`.**
   As in the libraries above, subtraction is addition of negated
   offsets; because of clamping it is not the inverse of `date.add`
   (e.g. `(date.sub (date.add (date.mk 2020 1 31) 0 1 0) 0 1 0)` is
   2020-01-29).

6. **Comparisons are chronological order** under the epoch-day
   bijection, and `=` holds iff two terms denote the same calendar
   day. In particular `(= (date.mk 2000 2 30) (date.mk 2000 3 1))` is
   true. The order is total: exactly one of `date.lt`, `=` (reversed
   `date.lt`) holds for any pair, `date.le` is `date.lt` or `=`, and
   `date.gt`/`date.ge` are the mirrored comparisons.

## Implementation overview

- `src/ast/date_decl_plugin.{h,cpp}` — sort, operators, values
  (normalized ground `date.mk` applications are the values of the
  theory and print as such in models), and the concrete + symbolic
  calendar conversions shared by all components. An internal operator
  `date.epoch : Date -> Int` (not exposed to SMT-LIB) names the
  epoch-day of a date term.
- `src/ast/rewriter/date_rewriter.{h,cpp}` — constant folding for all
  operations, `(date.add d 0 0 0) -> d`, and normalization of
  `date.gt`/`date.ge` into `date.lt`/`date.le`; wired into
  `th_rewriter`.
- `src/smt/theory_date.{h,cpp}` — legacy SMT core solver.
- `src/sat/smt/date_solver.{h,cpp}` — SAT/EUF core solver.
- `src/model/date_factory.h` — value factory for model construction.

Both solvers implement the same relevancy-friendly reduction: each
date term `t` gets an integer term `(date.epoch t)`; internalizing a
date operation asserts its defining axiom over epochs
(`date.mk`/`date.add`/`date.sub` fix the epoch of the result,
selectors equal the civil-from-days expressions of the argument's
epoch, comparisons are biconditional with epoch comparisons). The
epoch map is a bijection; injectivity is enforced lazily: merging two
epoch terms forces the dates equal, and a disequality between two
dates forces their epochs apart. Model values are decoded from the
arithmetic model of the epoch terms.
