; Arrays indexed by Date escape the supported fragment; the solver must
; reject them, not guess. (This one would otherwise be a wrong "sat":
; equal day numbers force c1 = c2, hence equal selects.)
; expect: error (and no sat/unsat answer)
(declare-const a (Array Date Int))
(declare-const c1 Date)
(declare-const c2 Date)
(assert (= (date.to_days c1) (date.to_days c2)))
(assert (= (select a c1) 1))
(assert (= (select a c2) 2))
(check-sat)
