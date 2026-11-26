; The forall has no inferable trigger, but the ground assertions alone are unsat.
(set-logic UFLIA)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (forall ((x Int)) (or (> x y) (< (+ x x) z))))
(assert (< y z))
(assert (> y z))
(check-sat)
