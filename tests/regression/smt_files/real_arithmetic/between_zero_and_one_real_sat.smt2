; Over the reals there is a value strictly between 0 and 1 (over the integers there
; is none, see between_zero_and_one_int_unsat.smt2).
(set-logic QF_LRA)
(declare-const x Real)
(assert (< 0 x))
(assert (< x 1))
(check-sat)
