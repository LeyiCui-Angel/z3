; symbolic offsets: adding n days moves the epoch by exactly n;
; there is exactly one n mapping 2000-01-01 to 2000-03-01
(declare-const n Int)
(assert (= (date.add (date.mk 2000 1 1) 0 0 n) (date.mk 2000 3 1)))
(assert (not (= n 60)))
(check-sat)
; EXPECT: unsat
