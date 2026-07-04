(set-logic ALL)
(declare-const d Date)
(assert (date.lt (date.add d 0 0 1) d))
(check-sat)
