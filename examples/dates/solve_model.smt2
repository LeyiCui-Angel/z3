; Solve for an unknown date: the only Tuesday of July 2026 with 5 < day < 10
; is 2026-07-07.
; expect: sat, day = 7
(declare-const d Date)
(assert (= (date.year d) 2026))
(assert (= (date.month d) 7))
(assert (= (date.dow d) 2))
(assert (> (date.day d) 5))
(assert (< (date.day d) 10))
(check-sat)
(get-value ((date.day d) (date.to_days d)))
