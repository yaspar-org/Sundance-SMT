(set-logic QF_LIA)
(declare-const var_8 Int)
(assert (= (+ 0 (* 1 var_8) 0) (+ 0 (* (- 1) var_8) 1)))  ; var_8 = -var_8 + 1 ==> 2*var_8 = 1 which is UNSAT b/c var_8 is Int
(check-sat)
