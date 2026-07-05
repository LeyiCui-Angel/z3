; like t05 but with room for exactly one model: d = 1970-01-02
(declare-const d Date)
(assert (date.gt d (date.mk 1969 12 31)))
(assert (date.lt d (date.mk 1970 1 3)))
(assert (distinct d (date.mk 1970 1 1)))
(check-sat)
(get-value (d (date.year d) (date.month d) (date.day d)))
; EXPECT: sat, d = (date.mk 1970 1 2)
