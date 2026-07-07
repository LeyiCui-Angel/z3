; Roundtrip/range theorems over a fully symbolic date. Each negation must be
; unsat; together they show the days-from-civil and civil-from-days formulas
; are mutually inverse and the accessors always yield a valid civil triple.
; expect: unsat, unsat, unsat, unsat
(declare-const d Date)
(assert (not (= (date.from_days (date.to_days d)) d)))
(check-sat)
(reset)
(declare-const d Date)
(assert (not (= (date.mk (date.year d) (date.month d) (date.day d)) d)))
(check-sat)
(reset)
(declare-const d Date)
(assert (not (date.valid (date.year d) (date.month d) (date.day d))))
(check-sat)
(reset)
; day overflow carries into following months (documented in the README)
(assert (not (= (date.mk 2026 6 37) (date.mk 2026 7 7))))
(check-sat)
