; regression: bug_reports/*/constraints_63 - February 30th cannot be
; constructed from the components of another date
(set-logic ALL)
(declare-const x Date)
(declare-const y Date)
(assert (= x (date.mk 2020 1 30)))
(assert (= y (date.mk (date.year x) 2 (date.day x))))
(assert (= (date.day x) 30))
(check-sat)
; EXPECT: unsat
