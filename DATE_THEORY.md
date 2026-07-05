# The Date Theory Extension

This checkout extends Z3 with a native theory of calendar dates, exposed
through the SMT-LIB front-end exactly as specified in `Dates.smt2`:

| symbol       | signature              | meaning                                    |
| ------------ | ---------------------- | ------------------------------------------ |
| `Date`       | sort                   | a day of the proleptic Gregorian calendar  |
| `date.mk`    | `Int Int Int -> Date`  | construct a date from year, month, day     |
| `date.year`  | `Date -> Int`          | year component                             |
| `date.month` | `Date -> Int`          | month component (1..12)                    |
| `date.day`   | `Date -> Int`          | day-of-month component (1..31)             |
| `date.add`   | `Date Int Int Int -> Date` | add year/month/day offsets             |
| `date.sub`   | `Date Int Int Int -> Date` | subtract year/month/day offsets        |
| `date.lt/le/gt/ge` | `Date Date -> Bool` | chronological comparison                |

Equality and `distinct` are the built-in Core operators.

## Semantics

The carrier of `Date` is the set of days of the **proleptic Gregorian
calendar** with astronomical year numbering: years extend indefinitely in
both directions, year 0 exists (and is a leap year), and the leap year
rule (divisible by 4, except centuries, except multiples of 400) is
applied to all years. Every `Date` value is in bijection with an integer
*epoch day number*, where day 0 is 1970-01-01. The bijection is
Howard Hinnant's `days_from_civil` / `civil_from_days` pair, which is
expressible in linear integer arithmetic with `div`/`mod` by constants.

Decisions taken where conventions differ:

1. **`date.mk` is total** (required by the task). Out-of-range arguments
   are normalized with the C `mktime` convention: the month is resolved
   first, with overflow and underflow carrying into the year
   (`months = 12*y + (m - 1)`; the resolved year is `months div 12` and
   the resolved month `months mod 12 + 1`); the day argument is then
   interpreted as an offset from day 1 of the resolved month, so
   out-of-range days walk forwards or backwards through the calendar.
   Examples:
   - `(date.mk 2000 2 30)` = 2000-03-01 (Feb 2000 has 29 days)
   - `(date.mk 1900 2 29)` = 1900-03-01 (1900 is not a leap year)
   - `(date.mk 2000 13 1)` = 2001-01-01
   - `(date.mk 2000 0 15)` = 1999-12-15
   - `(date.mk 2000 1 0)`  = 1999-12-31
   - `(date.mk 2000 1 400)` = 2001-02-03

2. **Selectors return the components of the normalized date**, so
   `(date.year (date.mk 2000 2 30))` is 2000, `date.month` of it is 3 and
   `date.day` of it is 1. Consequently `1 <= date.month d <= 12` and
   `1 <= date.day d <= 31` are valid for every date `d`, and
   `(date.mk (date.year d) (date.month d) (date.day d)) = d` is the
   identity.

3. **`date.add d py pm pd`** follows the dominant convention of date
   libraries (java.time, .NET, Python's `relativedelta`):
   - the year and month offsets are combined into a single month offset
     `12*py + pm` and added to the (year, month) of `d`;
   - the day-of-month is **clamped** to the length of the target month
     (Jan 31 + 1 month = Feb 28, or Feb 29 in leap years);
   - the day offset `pd` is then added as exact day arithmetic on the
     epoch number.
   Examples:
   - `(date.add (date.mk 2000 1 31) 0 1 0)` = 2000-02-29
   - `(date.add (date.mk 2000 2 29) 1 0 0)` = 2001-02-28
   - `(date.add (date.mk 2000 2 29) 1 1 0)` = 2001-03-29 (13 months, no clamp)
   - `(date.add (date.mk 2000 1 1) 0 0 60)` = 2000-03-01
   Note that clamping makes month addition non-invertible:
   `(date.sub (date.add (date.mk 2000 1 31) 0 1 0) 0 1 0)` = 2000-01-29.

4. **`date.sub d py pm pd` = `date.add d (- py) (- pm) (- pd)`** by
   definition. This mirrors `minusMonths`/`minusYears` of java.time.

5. **Comparisons are chronological**: `date.lt a b` iff the epoch day of
   `a` is smaller than the epoch day of `b`. `date.gt`/`date.ge` are the
   mirrored forms of `date.lt`/`date.le`.

6. **Equality is structural on the calendar**: two dates are equal iff
   their epoch days (equivalently, their normalized year/month/day
   triples) are equal. The sort has infinitely many elements, so
   `distinct` constraints over any number of date variables are
   satisfiable.

## Architecture

The implementation reduces the whole theory to linear integer
arithmetic through an internal (not user-visible) injection
`date.epoch! : Date -> Int`:

- `src/ast/date_decl_plugin.{h,cpp}` — sort/op declarations; `date_util`
  with both concrete (arbitrary-precision rational) and symbolic
  (term-level) implementations of the calendar maps. Canonical date
  values are `(date.mk y m d)` with normalized numeral arguments;
  `decl_plugin::is_value/is_unique_value` recognize them, making `=` and
  `distinct` on literals decidable in the rewriter.
- `src/ast/rewriter/date_rewriter.{h,cpp}` — constant folding for all
  operations, normalization `date.mk` -> canonical value,
  `date.gt/ge` -> mirrored `date.lt/le`, `date.sub` -> `date.add` with
  negated offsets. Plugged into `th_rewriter` and `model_evaluator`.
- `src/smt/theory_date.{h,cpp}` — legacy SMT core solver.
- `src/sat/smt/date_solver.{h,cpp}` — SAT/EUF core solver.
- `src/model/date_factory.h` — value factory producing canonical date
  values from epoch numbers.

Both solvers implement the same thin axiomatization:

- for `t = (date.mk y m d)`: `epoch(t) = epoch-of-ymd(y, m, d)`;
- for `t = (date.add d py pm pd)`: `epoch(t) = epoch-of-add(epoch(d), py, pm, pd)`;
- `date.sub` likewise with negated offsets;
- for selectors: `(date.year d) = year-of-epoch(epoch(d))` etc., plus the
  roundtrip identity `epoch(d) = days-from-civil(year, month, day of
  epoch(d))` and the component range facts (month in [1,12], day in
  [1,31]) — valid facts that let component equalities propagate to epoch
  equalities by congruence;
- for comparisons: `atom <=> epoch(a) < epoch(b)` (resp. `<=`);
- for every Date term: the tautology
  `(or (<= epoch(d) 0) (>= epoch(d) 0))`, whose only purpose is to
  register `epoch(d)` with the arithmetic solver so it always has a
  model value;
- injectivity `epoch(a) = epoch(b) => a = b`, asserted lazily for
  disequalities and at final check for distinct date classes whose
  epoch values coincide in the arithmetic model (the standard
  model-based theory combination step). The converse direction is
  congruence of `date.epoch!` and holds automatically.

All right-hand sides use only linear arithmetic, `ite`, and `div`/`mod`
by positive constants, so the reduction target is decidable. In the
legacy core the axioms are queued during internalization and flushed in
`propagate()`, because date terms are internalized re-entrantly from
within arithmetic atoms.

Models assign each date class the value `(date.mk y m d)` derived from
the arithmetic model value of its epoch; unconstrained dates default to
1970-01-01.

## Logic gating

The `Date` sort and `date.*` symbols are available when no `set-logic`
is given and under `(set-logic ALL)`. When date terms are present, the
legacy kernel's configuration is routed to the general setup so that
`theory_date` and the arithmetic solver are always registered; the
SAT/EUF core instantiates the date solver on demand by family id.

## Tests

`../tests/*.smt2` (relative to this directory in the task workspace)
exercise parsing, normalization, arithmetic, comparisons, injectivity,
congruence, models, and incremental solving; `../tests/run_tests.sh`
runs them under both the legacy core (default) and the SAT/EUF core
(`sat.euf=true tactic.default_tactic=sat`).
