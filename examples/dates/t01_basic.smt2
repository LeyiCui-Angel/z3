; basic parsing, selectors, models
; EXPECT: sat ((y 2000) (m 3) (dd 1))
(declare-const d Date)
(declare-const y Int)
(declare-const m Int)
(declare-const dd Int)
(assert (= d (date.mk 2000 2 30)))   ; normalizes to 2000-03-01
(assert (= y (date.year d)))
(assert (= m (date.month d)))
(assert (= dd (date.day d)))
(check-sat)
(get-value (y m dd))
