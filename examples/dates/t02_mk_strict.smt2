; date.mk is strict: out-of-range components denote no date, so
; constraints forcing them are unsat. Valid components are fine.
(declare-const d Date)
(push)
(assert (= d (date.mk 2000 2 30)))   ; leap feb has only 29 days
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= d (date.mk 1900 2 29)))   ; 1900 is not leap
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= d (date.mk 2000 13 1)))   ; month overflow does not wrap
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= d (date.mk 2000 0 15)))   ; month 0 does not underflow
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= d (date.mk 2000 1 0)))    ; day 0 does not underflow
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= d (date.mk 2000 4 31)))   ; April has 30 days
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= d (date.mk 2000 1 -30)))  ; negative day
(check-sat)
; EXPECT: unsat
(pop)
(push)
(assert (= d (date.mk 2004 2 29)))   ; valid leap date
(check-sat)
; EXPECT: sat
(pop)
(push)
(assert (= d (date.mk 2000 12 31)))  ; valid end of year
(check-sat)
; EXPECT: sat
(pop)
