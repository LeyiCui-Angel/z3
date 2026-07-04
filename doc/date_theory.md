# The Date Theory

This Z3 checkout extends the SMT-LIB2 front-end with a native theory of
calendar dates. The theory is available under `(set-logic ALL)` and when no
logic is set.

## Signature

| Symbol       | Sort                        | Meaning                              |
|--------------|-----------------------------|--------------------------------------|
| `Date`       | sort                        | calendar dates                       |
| `date.mk`    | `Int Int Int -> Date`       | constructor: year, month, day        |
| `date.year`  | `Date -> Int`               | year component                       |
| `date.month` | `Date -> Int`               | month component                      |
| `date.day`   | `Date -> Int`               | day component                        |
| `date.add`   | `Date Int Int Int -> Date`  | add year/month/day offsets           |
| `date.sub`   | `Date Int Int Int -> Date`  | subtract year/month/day offsets      |
| `date.lt/le/gt/ge` | `Date Date -> Bool`   | chronological comparisons            |

Equality and `distinct` are the built-in Core operators. There is no
`date.eq`.

## Semantics

The behavioral semantics were derived from the examples accompanying the
task setup (`examples/*.smt2`, expected verdict encoded in each filename)
plus the conventional meaning of calendar dates. The decisions, and the
evidence for each:

1. **Every `Date` value is a calendar-valid proleptic Gregorian date**:
   `1 <= month <= 12` and `1 <= day <= days_in_month(year, month)`, with the
   Gregorian leap rule `(y mod 4 = 0 and y mod 100 != 0) or y mod 400 = 0`.
   Years range over all integers (proleptic calendar; year 0 exists).
   *Evidence*: `ex_unsat_invalid_month` (no date has month 13),
   `ex_unsat_feb30` (no date has Feb 30), `ex_sat_symbolic_leap_year`
   (month=2, day=29 forces the leap-year condition on the year, with the
   rule spelled out in the comment), `ex_sat_symbolic_date_range` ("every
   symbolic Date value is calendar-valid").

2. **Selectors invert `date.mk` on valid triples**: for calendar-valid
   `(y, m, d)`, `date.year (date.mk y m d) = y`, etc.
   *Evidence*: `ex_sat_invalid_mk_is_total` states these selector axioms
   for valid triples.

3. **`date.mk` is total but unspecified on invalid triples**: any
   application of `date.mk` is well-sorted; an invalid triple denotes an
   *unspecified* valid date, with no constraint linking its components to
   the arguments. Being a function, congruence still applies: syntactically
   equal invalid applications denote the same date.
   *Evidence*: the task instruction ("do not reject any application of
   `date.mk` ... at parse or type-check time") and the comment in
   `ex_sat_symbolic_leap_year` ("applying date.mk to an invalid triple ...
   is unspecified").

4. **`date.add d py pm pd` follows the three-step algorithm** documented in
   the example comments:
   1. *Month normalization*: `t = month(d) + 12*py + pm - 1`,
      `y1 = year(d) + floor(t / 12)`, `m1 = (t mod 12) + 1`. Floor division
      handles negative offsets (borrowing from the year).
   2. *End-of-month clamp*: `d1 = min(day(d), days_in_month(y1, m1))`.
   3. *Day carry*: the result is the calendar date exactly `pd` days after
      `(y1, m1, d1)`, carrying across month and year boundaries in the
      proleptic Gregorian calendar.
   *Evidence*: the step-by-step traces in `ex_sat_accessor_after_add`,
   `ex_sat_eom_clamp_nonleap`, `ex_sat_eom_clamp_leap_boundary`,
   `ex_sat_leap_year_feb29`; `ex_unsat_add_one_day_identity` ("the day
   carry always advances the date by exactly one day");
   `ex_unsat_add_zero_changes_date` (zero offsets are the identity).

5. **`date.sub d py pm pd = date.add d (- py) (- pm) (- pd)`**.
   *Evidence*: `ex_unsat_subtract_positive_period` (subtracting 7 days
   yields a strictly earlier date), plus the standard interpretation of
   subtracting a period.

6. **Comparisons are chronological**, equivalent to the lexicographic order
   on `(year, month, day)`: `date.lt` is a strict total order and `le/gt/ge`
   are its variants.
   *Evidence*: `ex_sat_basic_comparison` ("lexicographic on (year, month,
   day)"), `ex_unsat_cyclic_ordering` ("date.lt is a strict total order").

7. **Equality is extensional**: dates with equal components are equal.
   *Evidence*: `ex_unsat_add_zero_changes_date` requires
   `date.add d 0 0 0 = d` even for a symbolic `d`, which is exactly
   extensionality over equal components.

## Implementation

The theory is implemented as a reduction to linear integer arithmetic.
For every term `t` of sort `Date` the solvers create the selector terms
`(date.year t)`, `(date.month t)`, `(date.day t)` and assert:

- *validity*: the component constraints of decision 1 (the
  `days_in_month` table is an `ite` expression; the leap rule uses `mod`
  by the constants 4, 100, 400);
- *operation definitions*: for `date.mk`, the guarded selector equations of
  decisions 2 and 3; for `date.add`/`date.sub`, the algorithm of decisions
  4 and 5.

The day carry and the comparisons go through the bijection between valid
dates and their **epoch day number** (days since 1970-01-01), using
H. Hinnant's `days_from_civil` algorithm. It uses only integer division
and modulus by positive constants, so the whole theory stays inside
decidable linear integer arithmetic. Every date term `t` gets an internal
shared epoch term `(date.epoch! t)` (an operator of the date family that
is *not* exposed through the SMT-LIB front-end), defined by
`date.epoch!(t) = days_from_civil(year t, month t, day t)`. On top of it:

- `date.add`/`date.sub` assert
  `date.epoch!(r) = days_from_civil(y1, m1, d1) + pd`, where `(y1, m1, d1)`
  is the clamped normalized base; when the month offset is a zero literal
  this collapses to the linear equation
  `date.epoch!(r) = date.epoch!(base) + pd` over shared epoch terms, so
  chains of date arithmetic compose linearly and identities such as
  `date.add d 0 0 1 = d` are refuted without reasoning about the epoch
  bijection. The result components are *not* defined constructively from
  the epoch: calendar validity plus the epoch definition already
  determine them (the epoch map is a bijection between valid dates and
  integers), and the redundant `civil_from_days` division towers
  measurably slow the arithmetic solvers on chained arithmetic
  (`civil_from_days` survives only in `date_util::days_to_civil`, the
  concrete C++ evaluator).
- comparisons are asserted with **two** equivalent definitions: the order
  on epoch day numbers, and the lexicographic order on the components.
  Each is entailed by the rest of the theory, and the arithmetic solver
  uses whichever route is shallow (epoch for day arithmetic, lexicographic
  for order-theoretic facts such as antisymmetry).

Extensionality (decision 7) is enforced per pipeline:

- the legacy solver (`smt::theory_date`) instantiates, at final check, the
  lemma `year(a)=year(b) & month(a)=month(b) & day(a)=day(b) => a = b` for
  any two date terms in distinct equivalence classes whose components agree
  in the current arithmetic model;
- the SAT/EUF solver (`date::solver`) equates every non-constructor date
  term `t` with `date.mk (date.year t) (date.month t) (date.day t)` when
  the term is axiomatized (the same shape datatype solvers use), so
  congruence plus the arithmetic solver's equality propagation over shared
  terms identifies dates with equal components.

Concrete-evaluation fast paths exist at three levels: `date_rewriter`
folds ground selectors/arithmetic/comparisons during simplification;
the axiom builders in `date_util` constant-fold while building the
definitions (in particular, a zero month offset skips normalization and
clamping, and a zero day offset skips the epoch conversion entirely); and
ground `date.mk`/`date.add`/`date.sub` chains are evaluated outright
(`date_util::eval_ground`), asserting exact component values.

Models assign every `Date` class the value `(date.mk y m d)` built from
the arithmetic model of its selector terms; these values are always
calendar-valid.

### Source layout

| File | Role |
|------|------|
| `src/ast/date_decl_plugin.{h,cpp}` | sort/ops declarations, `date_util` (recognizers, calendar arithmetic, axiom builders) |
| `src/ast/rewriter/date_rewriter.{h,cpp}` | ground evaluation fast paths (hooked into `th_rewriter` and `model_evaluator`) |
| `src/model/date_factory.h` | value factory for model construction |
| `src/smt/theory_date.{h,cpp}` | legacy SMT-core theory solver |
| `src/sat/smt/date_solver.{h,cpp}` | SAT/EUF-core theory solver |

Registration touch points: `src/ast/reg_decl_plugins.cpp`,
`src/cmd_context/cmd_context.{h,cpp}` (`logic_has_date`),
`src/ast/rewriter/th_rewriter.cpp`, `src/model/model_evaluator.cpp`,
`src/smt/smt_setup.{h,cpp}`, `src/sat/smt/euf_solver.cpp`.

### Tests

Besides the 16 examples of the task setup, `examples/SMT-LIB2/dates/`
contains a 23-case regression suite (expected verdicts in the filenames)
covering ite-linkage of ground dates, extensionality, proleptic years,
century leap rules, invalid-constructor congruence, order-theoretic facts
and incremental solving.

### Running

The legacy pipeline is the default:

    z3 file.smt2

The SAT/EUF pipeline:

    z3 sat.euf=true tactic.default_tactic=sat file.smt2
