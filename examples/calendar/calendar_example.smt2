; Showcase for the theory of calendar dates.
; Run: z3 calendar_example.smt2

; 1. Ground evaluation: what day of the week was 2000-01-01?
(simplify (date.day-of-week (date.to-epoch 2000 1 1)))          ; 6 = Saturday

; 2. Find the first Friday the 13th after 2026-07-12.
(declare-const e Int)
(assert (> e (date.to-epoch 2026 7 12)))
(assert (= (date.day e) 13))
(assert (= (date.day-of-week e) 5))
(minimize e)
(check-sat)
(get-value (e (date.year e) (date.month e)))                    ; 2026-11-13

(reset)

; 3. Prove: no month can start and end on the same weekday
;    unless it has exactly 29 days (i.e. only leap-year February).
(declare-const y Int) (declare-const m Int)
(assert (and (<= 1 m) (<= m 12)))
(define-fun first () Int (date.to-epoch y m 1))
(define-fun last  () Int (date.to-epoch y m (date.days-in-month y m)))
(assert (= (date.day-of-week first) (date.day-of-week last)))
(assert (not (and (= m 2) (date.leap-year y))))
(check-sat)                                                     ; unsat

(reset)

; 4. A scheduling puzzle: a certificate issued on some valid date in 2026
;    expires exactly 90 days later; the expiry must fall in 2026 on a
;    weekend. When is the latest possible issue date?
(declare-const iy Int) (declare-const im Int) (declare-const id Int)
(assert (and (date.valid iy im id) (= iy 2026)))
(define-fun issue  () Int (date.to-epoch iy im id))
(define-fun expiry () Int (+ issue 90))
(assert (= (date.year expiry) 2026))
(assert (or (= (date.day-of-week expiry) 0) (= (date.day-of-week expiry) 6)))
(maximize issue)
(check-sat)
(get-value (im id (date.month expiry) (date.day expiry) (date.day-of-week expiry)))
