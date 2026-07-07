; Day arithmetic across month/year/leap boundaries.
; expect: unsat
(declare-const d Date)
(declare-const n Int)
(assert (not (and
  (= (date.add_days (date.mk 2024 2 28) 1) (date.mk 2024 2 29))
  (= (date.add_days (date.mk 2024 2 28) 2) (date.mk 2024 3 1))
  (= (date.add_days (date.mk 2023 2 28) 1) (date.mk 2023 3 1))
  (= (date.add_days (date.mk 1999 12 31) 1) (date.mk 2000 1 1))
  (= (date.add_days (date.mk 1900 2 28) 1) (date.mk 1900 3 1))
  (= (date.sub (date.mk 2026 7 7) (date.mk 1970 1 1)) 20641)
  (= (date.sub (date.mk 2000 1 1) (date.mk 2000 3 1)) (- 60))
  ; symbolic: adding then subtracting is the identity
  (= (date.sub (date.add_days d n) d) n)
  (= (date.add_days d 0) d)
  ; a week later is the same day of the week
  (= (date.dow (date.add_days d 7)) (date.dow d))
)))
(check-sat)
