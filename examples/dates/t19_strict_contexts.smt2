; strictness is independent of the shape of the constraint: any
; constraint set containing an out-of-range date.mk occurrence is unsat,
; and preprocessing must not discard the occurrence.
(declare-const y Date)
(declare-const b Bool)
(push)
(assert (not (= y (date.mk 2020 2 30))))  ; negative occurrence
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= y (ite b (date.mk 2020 2 30) (date.mk 2020 1 1))))
(check-sat)
; EXPECT: unsat (both branches are occurrences)
(pop)
(push)
(assert (distinct (date.mk 2020 2 30) (date.mk 2020 3 1)))
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= (date.mk 2020 2 30) (date.mk 2020 3 1)))
(check-sat)
; EXPECT: unsat (no normalization; and Feb 30 is no date at all)
(pop)
