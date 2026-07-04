(set-logic ALL)
(declare-const d Date)
(assert (not (date.le d (date.add d 0 0 0))))
(check-sat)
