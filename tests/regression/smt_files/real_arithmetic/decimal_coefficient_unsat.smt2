; 0.5 * y = 0.25 forces y = 1/2.
(set-logic QF_LRA)
(declare-const y Real)
(assert (<= (* 0.5 y) 0.25))
(assert (>= (* 0.5 y) 0.25))
(assert (= y 1))
(check-sat)
