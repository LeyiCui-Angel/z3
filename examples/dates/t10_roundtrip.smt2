; the constructor-selector roundtrip is the identity on dates
(declare-const d Date)
(assert (not (= d (date.mk (date.year d) (date.month d) (date.day d)))))
(check-sat)
; EXPECT: unsat
