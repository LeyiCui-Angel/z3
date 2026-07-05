; a free date constant gets a model value; distinct constants get
; distinct values
(declare-const d1 Date)
(declare-const d2 Date)
(declare-const d3 Date)
(assert (distinct d1 d2 d3))
(check-sat)
(get-value (d1 d2 d3))
; EXPECT: sat, three distinct (date.mk ...) values
