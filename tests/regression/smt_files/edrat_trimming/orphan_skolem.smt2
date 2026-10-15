; The refutation instantiates the forall with the Skolem constant of the exists,
; but never uses the Skolemization clause itself. A trimmed eDRAT proof must
; still declare the Skolem constant.
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun P (Int) Bool)
(assert (exists ((x Int)) (P (f x))))
(assert (forall ((y Int)) (! (and (= (f y) 0) (= (f y) 1)) :pattern ((f y)))))
(check-sat)
