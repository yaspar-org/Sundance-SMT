; x = (g x) does not define x (x occurs on both sides), so x must not be eliminated.
(set-logic UFLIA)
(declare-fun g (Int) Int)
(assert (forall ((x Int)) (=> (= x (g x)) (> x 0))))
(assert (= (g 0) 0))
(check-sat)
