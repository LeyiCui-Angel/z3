; date.add / date.sub semantics: combined month addition with day clamping,
; then exact day arithmetic. date.sub d py pm pd = date.add d -py -pm -pd.
(assert (or
  (not (= (date.add (date.mk 2000 1 31) 0 1 0) (date.mk 2000 2 29)))  ; clamp to leap feb
  (not (= (date.add (date.mk 1999 1 31) 0 1 0) (date.mk 1999 2 28)))  ; clamp to feb
  (not (= (date.add (date.mk 2000 2 29) 1 0 0) (date.mk 2001 2 28)))  ; clamp on year step
  (not (= (date.add (date.mk 2000 2 29) 1 1 0) (date.mk 2001 3 29)))  ; combined 13 months, no clamp
  (not (= (date.add (date.mk 2000 1 1) 0 0 60) (date.mk 2000 3 1)))   ; exact day arithmetic
  (not (= (date.add (date.mk 2000 1 1) 0 -1 0) (date.mk 1999 12 1)))  ; negative month offset
  (not (= (date.add (date.mk 2000 1 1) 0 0 0) (date.mk 2000 1 1)))    ; identity
  (not (= (date.sub (date.mk 2000 3 31) 0 1 0) (date.mk 2000 2 29)))  ; sub with clamp
  (not (= (date.sub (date.mk 2000 1 1) 0 0 1) (date.mk 1999 12 31)))  ; sub one day
  (not (= (date.sub (date.mk 2000 1 1) 1 2 3) (date.add (date.mk 2000 1 1) -1 -2 -3)))
))
(check-sat)
; EXPECT: unsat
