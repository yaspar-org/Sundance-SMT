; The integer counterpart of between_zero_and_one_real_sat.smt2.
(set-logic QF_LIA)
(declare-const n Int)
(assert (< 0 n))
(assert (< n 1))
(check-sat)
