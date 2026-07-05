; symbolic reasoning: d strictly between 1969-12-31 and 1970-01-03,
; distinct from 1970-01-01 and 1970-01-02 => unsat
(declare-const d Date)
(assert (date.gt d (date.mk 1969 12 31)))
(assert (date.lt d (date.mk 1970 1 3)))
(assert (distinct d (date.mk 1970 1 1)))
(assert (distinct d (date.mk 1970 1 2)))
(check-sat)
; EXPECT: unsat
