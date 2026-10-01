; A forall with a ground body is instantiated to the body term itself, which
; is stored in terms_list without an egraph node. Its literal must not be
; observed by CaDiCaL, or process_assignment panics in to_egraph_id.
(set-logic UFLIA)
(declare-fun f (Int) Bool)
(declare-fun g (Int) Bool)
(assert (forall ((x Int)) (! (=> true true) :pattern ((f x)))))
(assert (f 1))
(assert (or (g 1) (g 2)))
(assert (not (g 1)))
(check-sat)
