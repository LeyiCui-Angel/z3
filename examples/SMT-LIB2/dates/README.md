# Date theory regression tests

SMT-LIB2 files exercising the calendar date theory (see `doc/date_theory.md`).
The expected verdict is encoded in each filename (`_sat` / `_unsat`);
`t17_incremental.smt2` issues four `check-sat` commands and expects
`unsat sat unsat sat`.

Run through the legacy SMT core (default):

    z3 tNN_....smt2

and through the SAT/EUF core:

    z3 sat.euf=true tactic.default_tactic=sat tNN_....smt2

Known limitation: `t22_add_assoc_sat.smt2` (chained symbolic date.add with
day offsets) solves in under two seconds on the legacy core but exceeds
reasonable time limits on the SAT/EUF core. The bottleneck is the SAT/EUF
arithmetic solver on the coupled epoch-conversion divisions: the pure
linear-integer-arithmetic rendering of the same constraints, with no date
theory involved, shows the same asymmetry between the two arithmetic cores.
