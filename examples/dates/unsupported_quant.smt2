; Quantification over Date escapes the supported fragment; the solver must
; reject it, not guess. (This one would otherwise be a wrong "sat":
; date.to_days is surjective, so the assertion is false.)
; expect: error (and no sat/unsat answer)
(assert (forall ((d Date)) (not (= (date.to_days d) 5))))
(check-sat)
