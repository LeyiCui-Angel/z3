; Property (validity) tests for the calendar-date theory.
;
; Each labeled block asserts the NEGATION of a statement that is valid in the
; theory of calendar dates and must therefore print "unsat".  The final two
; blocks are satisfiable sanity checks (they must print "sat") guarding
; against the tests passing vacuously.

(set-option :timeout 300000)

(declare-const y Int)
(declare-const m Int)
(declare-const d Int)
(declare-const n Int)

(echo "leap-400-cycle")
(push)
(assert (not (= (date.is-leap-year y) (date.is-leap-year (+ y 400)))))
(check-sat)
(pop)

(echo "dow-range")
(push)
(assert (not (and (<= 0 (date.day-of-week n)) (<= (date.day-of-week n) 6))))
(check-sat)
(pop)

(echo "dow-weekly")
(push)
(assert (not (= (date.day-of-week (+ n 7)) (date.day-of-week n))))
(check-sat)
(pop)

(echo "epoch-400-shift")
(push)
(assert (not (= (date.to-epoch (+ y 400) m d) (+ (date.to-epoch y m d) 146097))))
(check-sat)
(pop)

(echo "month-range")
(push)
(assert (not (and (<= 1 (date.month n)) (<= (date.month n) 12))))
(check-sat)
(pop)

(echo "day-range")
(push)
(assert (not (and (<= 1 (date.day n)) (<= (date.day n) 31))))
(check-sat)
(pop)

(echo "day-in-month")
(push)
(assert (not (<= (date.day n) (date.days-in-month (date.year n) (date.month n)))))
(check-sat)
(pop)

(echo "fields-valid")
(push)
(assert (not (date.valid (date.year n) (date.month n) (date.day n))))
(check-sat)
(pop)

(echo "roundtrip-epoch")
(push)
(assert (not (= (date.to-epoch (date.year n) (date.month n) (date.day n)) n)))
(check-sat)
(pop)

(echo "roundtrip-fields")
(push)
(assert (date.valid y m d))
(assert (not (and (= (date.year  (date.to-epoch y m d)) y)
                  (= (date.month (date.to-epoch y m d)) m)
                  (= (date.day   (date.to-epoch y m d)) d))))
(check-sat)
(pop)

(echo "next-day")
(push)
(assert (date.valid y m d))
(assert (< d (date.days-in-month y m)))
(assert (not (= (date.to-epoch y m (+ d 1)) (+ (date.to-epoch y m d) 1))))
(check-sat)
(pop)

(echo "new-year")
(push)
(assert (not (= (date.to-epoch (+ y 1) 1 1) (+ (date.to-epoch y 12 31) 1))))
(check-sat)
(pop)

(echo "monotone")
(push)
(declare-const y2 Int)
(declare-const m2 Int)
(declare-const d2 Int)
(assert (date.valid y m d))
(assert (date.valid y2 m2 d2))
(assert (or (< y y2)
            (and (= y y2) (< m m2))
            (and (= y y2) (= m m2) (< d d2))))
(assert (>= (date.to-epoch y m d) (date.to-epoch y2 m2 d2)))
(check-sat)
(pop)

(echo "sat-sanity-leap")
(push)
(assert (date.is-leap-year y))
(assert (> y 2026))
(check-sat)
(pop)

(echo "sat-sanity-feb29")
(push)
(assert (date.valid y 2 29))
(assert (not (date.is-leap-year (+ y 4))))
(check-sat)
(pop)
