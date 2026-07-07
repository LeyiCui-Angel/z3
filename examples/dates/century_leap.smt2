; Century leap-year rule: the only century year with a Feb 29 between 1800
; and 2200 is 2000.
; expect: sat, y = 2000, then unsat
(declare-const y Int)
(assert (date.valid y 2 29))
(assert (= 0 (mod y 100)))
(assert (<= 1800 y 2200))
(check-sat)
(get-value (y))
(assert (not (= y 2000)))
(check-sat)
