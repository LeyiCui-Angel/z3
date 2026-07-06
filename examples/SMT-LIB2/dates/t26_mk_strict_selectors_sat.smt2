; Strict date.mk with a symbolic year: the selectors equal the arguments,
; so year(y) = l, and validity forces l to be a leap year in [2004, 2010].
(set-logic ALL)
(declare-const l Int)
(declare-const y Date)
(assert (= y (date.mk l 2 29)))
(assert (>= l 2004))
(assert (<= l 2010))
(assert (= (date.year y) l))
(check-sat)
