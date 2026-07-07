; Invert the constructor by solving: which valid y/m/d has day number 20641?
; expect: sat, y = 2026, m = 7, d = 7
(declare-const y Int)
(declare-const m Int)
(declare-const d Int)
(assert (date.valid y m d))
(assert (= (date.mk y m d) (date.from_days 20641)))
(check-sat)
(get-value (y m d))
; without the validity guard the constructor still normalizes: 2026-06-37
; denotes the same day (June has 30 days, so day 37 wraps to July 7).
(assert (not (= (date.mk 2026 6 37) (date.from_days 20641))))
(check-sat)
