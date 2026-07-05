; selector ranges hold for every date
(declare-const d Date)
(assert (or (< (date.month d) 1) (> (date.month d) 12)
            (< (date.day d) 1) (> (date.day d) 31)))
(check-sat)
; EXPECT: unsat
