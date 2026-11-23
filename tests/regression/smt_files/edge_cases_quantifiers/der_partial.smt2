; Only x is eliminated; z remains and is instantiated through the inferred trigger (f z).
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun y () Int)
(assert (forall ((x Int) (z Int)) (or (not (= (+ y 2) x)) (> (f z) x))))
(assert (< (f 5) (+ y 1)))
(check-sat)
