; dates are determined by their components: equal selectors => equal dates
(declare-const d1 Date)
(declare-const d2 Date)
(assert (= (date.year d1) (date.year d2)))
(assert (= (date.month d1) (date.month d2)))
(assert (= (date.day d1) (date.day d2)))
(assert (distinct d1 d2))
(check-sat)
; EXPECT: unsat
