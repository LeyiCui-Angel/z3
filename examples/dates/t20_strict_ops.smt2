; strictness through the other operations: selectors, arithmetic and
; comparisons over an invalid construction are unsat as well
(declare-const w Date)
(declare-const k Int)
(push)
(assert (= k (date.year (date.mk 2020 2 30))))
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= w (date.add (date.mk 2020 2 30) 0 0 1)))
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (date.lt (date.mk 2020 2 30) (date.mk 2020 3 5)))
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (not (date.lt (date.mk 2020 2 30) (date.mk 2020 3 5))))
(check-sat)
; EXPECT: unsat (polarity does not matter)
(pop)
(push)
(assert (= w (date.sub (date.mk 2023 2 29) 0 1 0)))
(check-sat)
; EXPECT: unsat (2023 is not leap)
(pop)
