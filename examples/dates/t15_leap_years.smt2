; leap year rules: div-by-4 except centuries, unless div-by-400
(assert (or
  (not (= (date.day (date.mk 2000 2 29)) 29))   ; 2000 leap (400)
  (not (= (date.day (date.mk 2400 2 29)) 29))   ; 2400 leap (400)
  (= (date.day (date.mk 1900 2 29)) 29)         ; 1900 not leap (100)
  (= (date.day (date.mk 2100 2 29)) 29)         ; 2100 not leap (100)
  (not (= (date.day (date.mk 2024 2 29)) 29))   ; 2024 leap (4)
  (= (date.day (date.mk 2023 2 29)) 29)         ; 2023 not leap
  (not (= (date.day (date.mk 0 2 29)) 29))      ; year 0 leap (400)
  (not (= (date.day (date.mk -4 2 29)) 29))     ; year -4 leap (proleptic)
))
(check-sat)
; EXPECT: unsat
