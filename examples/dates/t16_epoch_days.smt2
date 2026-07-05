; day-difference reasoning across a leap boundary:
; from 2024-02-28, adding 2 days lands on 2024-03-01;
; from 2023-02-28, adding 2 days lands on 2023-03-02.
(assert (or
  (not (= (date.add (date.mk 2024 2 28) 0 0 2) (date.mk 2024 3 1)))
  (not (= (date.add (date.mk 2023 2 28) 0 0 2) (date.mk 2023 3 2)))
))
(check-sat)
; EXPECT: unsat
