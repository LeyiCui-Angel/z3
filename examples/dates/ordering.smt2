; Ordering behaves like a strict total order compatible with equality.
; expect: unsat
(declare-const d1 Date)
(declare-const d2 Date)
(declare-const d3 Date)
(assert (or
  ; antisymmetry
  (and (date.lt d1 d2) (date.lt d2 d1))
  ; transitivity
  (and (date.lt d1 d2) (date.lt d2 d3) (not (date.lt d1 d3)))
  ; totality
  (and (not (date.lt d1 d2)) (not (date.lt d2 d1)) (not (= d1 d2)))
  ; le = lt or eq
  (and (date.le d1 d2) (not (date.lt d1 d2)) (not (= d1 d2)))))
(check-sat)
