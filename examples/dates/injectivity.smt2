; date.to_days / date.from_days form a bijection: a date is determined by its
; day number, and dates with equal fields are equal.
; expect: unsat
(declare-const c Date)
(declare-const e Date)
(assert (or
  (and (= (date.to_days c) 5) (not (= c (date.from_days 5))))
  (and (= (date.to_days c) (date.to_days e)) (not (= c e)))
  (and (= (date.year c) (date.year e))
       (= (date.month c) (date.month e))
       (= (date.day c) (date.day e))
       (not (= c e)))
  ; distinct over Date is decided through the same bijection
  (and (distinct c e (date.from_days 3)) (= (date.to_days c) 3))))
(check-sat)
