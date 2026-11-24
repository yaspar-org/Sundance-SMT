; In QF_LRA, 1 and 1.0 are the same Real constant.
(set-logic QF_LRA)
(declare-const x Real)
(assert (= x 1))
(assert (= x 1.0))
(assert (= x (/ 2 2)))
(check-sat)
