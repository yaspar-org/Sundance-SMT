; As der_forall.smt2, but satisfiable: after eliminating x no quantifier is left.
(set-logic UFLIA)
(declare-fun y () Int)
(assert (forall ((x Int)) (=> (= x (+ y 1)) (= x 19))))
(assert (= y 18))
(check-sat)
