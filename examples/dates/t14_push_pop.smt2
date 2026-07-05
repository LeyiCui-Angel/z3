; incremental solving
(declare-const d Date)
(assert (date.ge d (date.mk 2020 1 1)))
(push)
(assert (date.lt d (date.mk 2019 1 1)))
(check-sat)
; EXPECT: unsat
(pop)
(assert (date.le d (date.mk 2020 1 1)))
(check-sat)
(get-value (d))
; EXPECT: sat, d = 2020-01-01
(push)
(assert (distinct d (date.mk 2020 1 1)))
(check-sat)
; EXPECT: unsat
(pop)
