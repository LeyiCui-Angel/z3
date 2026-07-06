; date.mk does not normalize month overflow: month 14 (reached through
; arithmetic over selectors) is invalid, so the constraints are unsat.
(set-logic ALL)
(declare-const a Date)
(declare-const b Date)
(assert (= a (date.mk 2025 6 15)))
(assert (= b (date.mk (date.year a) (+ (date.month a) 8) (date.day a))))
(check-sat)
