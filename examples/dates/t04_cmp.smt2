; comparisons are chronological
(assert (or
  (not (date.lt (date.mk 2024 2 29) (date.mk 2024 3 1)))
  (not (date.le (date.mk 2024 2 29) (date.mk 2024 2 29)))
  (date.lt (date.mk 2024 2 29) (date.mk 2024 2 29))
  (not (date.gt (date.mk 2024 3 1) (date.mk 2024 2 29)))
  (not (date.ge (date.mk 2024 3 1) (date.mk 2024 3 1)))
  (not (date.lt (date.mk 1969 12 31) (date.mk 1970 1 1)))
  (not (date.lt (date.mk -1 12 31) (date.mk 0 1 1)))   ; proleptic year 0 exists
))
(check-sat)
; EXPECT: unsat
