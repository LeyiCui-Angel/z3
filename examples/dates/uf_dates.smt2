; Supported residue: uninterpreted functions *returning* Date from Date-free
; domains, and quantification over Int (not Date) with date terms inside.
; expect: sat, unsat, sat
(declare-fun f (Int) Date)
(assert (= (f 0) (date.mk 2020 1 1)))
(assert (date.lt (f 1) (f 0)))
(check-sat)
(assert (= (date.year (f 1)) 2021))
(check-sat)
(reset)
(declare-const d Date)
(assert (forall ((n Int)) (= (date.sub (date.add_days d n) d) n)))
(check-sat)
