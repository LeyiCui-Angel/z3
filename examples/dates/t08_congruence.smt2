; injectivity must interact soundly with congruence for uninterpreted
; functions over dates
(declare-const d1 Date)
(declare-const d2 Date)
(declare-fun f (Date) Int)
(assert (date.le d1 d2))
(assert (date.ge d1 d2))     ; together: same epoch => d1 = d2
(assert (not (= (f d1) (f d2))))
(check-sat)
; EXPECT: unsat
