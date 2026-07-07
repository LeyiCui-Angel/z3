; Datatypes with Date components escape the arithmetic reduction; the solver
; must reject them rather than decide them (a wrong verdict would be unsound).
; expect: error, no sat/unsat
(declare-datatype Pair ((pair (fst Date) (snd Int))))
(declare-const p Pair)
(assert (= (fst p) (date.mk 2020 1 1)))
(check-sat)
