; date.mk is total; out-of-range arguments normalize (mktime convention)
; each assertion is a negation of an expected identity => unsat
(assert (or
  (not (= (date.mk 2000 2 30) (date.mk 2000 3 1)))    ; day overflow (leap feb)
  (not (= (date.mk 1900 2 29) (date.mk 1900 3 1)))    ; 1900 is not leap
  (not (= (date.mk 2000 13 1) (date.mk 2001 1 1)))    ; month overflow
  (not (= (date.mk 2000 0 15) (date.mk 1999 12 15)))  ; month underflow
  (not (= (date.mk 2000 1 0)  (date.mk 1999 12 31)))  ; day zero
  (not (= (date.mk 2000 1 -30) (date.mk 1999 12 1)))  ; negative day
  (not (= (date.mk 2000 -1 1) (date.mk 1999 11 1)))   ; negative month
  (not (= (date.mk 2004 2 29) (date.mk 2004 2 29)))   ; leap year valid date
  (not (= (date.mk 2000 1 400) (date.mk 2001 2 3)))   ; large day offset
))
(check-sat)
; EXPECT: unsat
