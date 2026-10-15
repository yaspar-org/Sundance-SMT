; The instance x := 0, y := 0 of the forall is (or (not (P 0)) (not (P 0))),
; whose Tseitin clause lists (not (P 0)) twice. eDRAT proof steps must not
; repeat a literal.
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun g (Int) Int)
(assert (forall ((x Int) (y Int)) (! (or (not (P x)) (not (P y))) :pattern ((g x) (g y)))))
(assert (= (g 0) 0))
(assert (P 0))
(check-sat)
