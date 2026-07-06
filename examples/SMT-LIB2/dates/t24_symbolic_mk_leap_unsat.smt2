; A date.mk with symbolic year, month 2, day 29 forces the year to be a
; leap year. No year in [2100, 2103] is one (2100 is a century non-leap).
(set-logic ALL)
(declare-const l Int)
(declare-const z Date)
(assert (= z (date.mk l 2 29)))
(assert (>= l 2100))
(assert (<= l 2103))
(check-sat)
