; leap year rules: div-by-4 except centuries, unless div-by-400.
; (date.mk y 2 29) is a date exactly for leap years y.
(declare-const y Int)
(declare-const d Date)
(assert (= d (date.mk y 2 29)))
(push)
(assert (= y 2000))    ; leap (400)
(check-sat)
; EXPECT: sat
(pop)
(push)
(assert (= y 2400))    ; leap (400)
(check-sat)
; EXPECT: sat
(pop)
(push)
(assert (= y 1900))    ; not leap (100)
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= y 2100))    ; not leap (100)
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= y 2024))    ; leap (4)
(check-sat)
; EXPECT: sat
(pop)
(push)
(assert (= y 2023))    ; not leap
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= y 0))       ; year 0 is leap (400)
(check-sat)
; EXPECT: sat
(pop)
(push)
(assert (= y -4))      ; proleptic: year -4 is leap
(check-sat)
; EXPECT: sat
(pop)
