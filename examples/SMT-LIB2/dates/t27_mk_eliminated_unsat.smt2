; The invalid constructor application is the only occurrence of y, so
; preprocessing may substitute y away; the strictness guard must survive.
(set-logic ALL)
(declare-const y Date)
(assert (= y (date.mk 2020 2 30)))
(check-sat)
