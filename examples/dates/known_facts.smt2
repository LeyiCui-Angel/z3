; Known calendar facts. The negated conjunction must be unsat.
; expect: unsat
(assert (not (and
  ; epoch and day numbers (days since 1970-01-01)
  (= (date.to_days (date.mk 1970 1 1)) 0)
  (= (date.to_days (date.mk 2000 3 1)) 11017)
  (= (date.to_days (date.mk 2026 7 7)) 20641)
  (= (date.to_days (date.mk 1999 12 31)) 10956)
  (= (date.to_days (date.mk 1 1 1)) (- 719162))
  (= (date.to_days (date.mk 9999 12 31)) 2932896)
  ; accessors invert from_days
  (= (date.year  (date.from_days 11017)) 2000)
  (= (date.month (date.from_days 11017)) 3)
  (= (date.day   (date.from_days 11017)) 1)
  (= (date.year  (date.from_days (- 719162))) 1)
  (= (date.month (date.from_days (- 719162))) 1)
  (= (date.day   (date.from_days (- 719162))) 1)
  ; ISO day of week: 1 = Monday ... 7 = Sunday
  (= (date.dow (date.mk 1970 1 1)) 4)   ; Thursday
  (= (date.dow (date.mk 2026 7 7)) 2)   ; Tuesday
  (= (date.dow (date.mk 1582 10 15)) 5) ; Friday (proleptic Gregorian)
  ; leap years
  (date.leap_year 2000)
  (not (date.leap_year 1900))
  (date.leap_year 2024)
  (not (date.leap_year 2023))
  (date.leap_year 0)
  ; validity
  (date.valid 2000 2 29)
  (not (date.valid 1900 2 29))
  (date.valid 2024 2 29)
  (not (date.valid 2023 2 29))
  (date.valid 2023 4 30)
  (not (date.valid 2023 4 31))
  (date.valid 2023 12 31)
  (not (date.valid 2023 13 1))
  (not (date.valid 2023 0 10))
  (not (date.valid 2023 1 0))
)))
(check-sat)
