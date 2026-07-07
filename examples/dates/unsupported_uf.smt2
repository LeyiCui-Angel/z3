; Uninterpreted functions taking Date arguments escape the fragment decided
; by the arithmetic reduction; the solver must reject them, not guess.
; expect: error (and no sat/unsat answer)
(declare-const c Date)
(declare-fun f (Date) Int)
(assert (= (f c) 0))
(check-sat)
