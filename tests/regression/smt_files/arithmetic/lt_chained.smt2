(set-logic QF_LIA)
(declare-const x Int)
(assert (< 1 x 2))
(check-sat)
