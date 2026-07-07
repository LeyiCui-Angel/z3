; The accessors invert date.mk on every valid symbolic triple (y, m, d).
; expect: unsat
(declare-const y Int)
(declare-const m Int)
(declare-const d Int)
(assert (date.valid y m d))
(assert (not (and (= (date.year (date.mk y m d)) y)
                  (= (date.month (date.mk y m d)) m)
                  (= (date.day (date.mk y m d)) d))))
(check-sat)
