; date.mk is strict: 2023 is not a leap year, so (date.mk 2023 2 29) has no
; calendar-valid interpretation and the equation is unsatisfiable.
(set-logic ALL)
(declare-const a Date)
(assert (= a (date.mk 2023 2 29)))
(assert (= (date.day a) 15))
(check-sat)
