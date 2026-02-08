(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)

(declare-sort %%Function%% 0)

(declare-sort Poly 0)
(declare-fun B (Bool) Poly)
(declare-fun %B (Poly) Bool)
(declare-fun apply (Poly Poly) Poly)
(declare-fun contains (Poly Poly) Bool)
(declare-fun union (Poly Poly) Poly)
(declare-fun intersection (Poly Poly) Poly)
(declare-const s1! Poly)
(declare-const s2! Poly)
(declare-const s3! Poly)
(declare-const a Poly)
;(assert (forall ((x Poly)) (! (= (B (%B x)) x) :pattern ((%B x)) )))
; instantiations
(assert (= (B (%B (apply (intersection s1! s2!) a))) (apply (intersection s1! s2!) a)))
(assert (= (B (%B (apply (intersection s1! s3!) a))) (apply (intersection s1! s3!) a)))
(assert (= (B (%B (apply s1! a))) (apply s1! a)))
(assert (= (B (%B (apply (union s2! s3!) a))) (apply (union s2! s3!) a)))
(assert (= (B (%B (apply (intersection s1! (union s2! s3!)) a))) (apply (intersection s1! (union s2! s3!)) a)))
(assert (= (B (%B (apply (union (intersection s1! s2!) (intersection s1! s3!)) a))) (apply (union (intersection s1! s2!) (intersection s1! s3!)) a)))


; note we need this contains even with 
;(assert (forall ((f! Poly) (a! Poly)) (!  (= (contains f! a!) (%B (apply (%Poly%fun%1. f!) a!))) :pattern ((contains f! a!)) )))
; instantiations
(assert (= (contains (intersection s1! s2!) a) (%B (apply (intersection s1! s2!) a))))
(assert (= (contains (intersection s1! s3!) a) (%B (apply (intersection s1! s3!) a))))
(assert (= (contains s1! a) (%B (apply s1! a))))
(assert (= (contains (union s2! s3!) a) (%B (apply (union s2! s3!) a))))
(assert (= (contains (intersection s1! (union s2! s3!)) a) (%B (apply (intersection s1! (union s2! s3!)) a))))
(assert (= (contains (union (intersection s1! s2!) (intersection s1! s3!)) a) (%B (apply (union (intersection s1! s2!) (intersection s1! s3!)) a))))


; I think we are missing one of these
(assert (forall ((%%hole%%2 Poly)(%%hole%%5 Poly) (x$ Poly)) (! (= (apply (union %%hole%%2 %%hole%%5) x$) (B (or (contains %%hole%%2 x$) (contains %%hole%%5 x$)))) :pattern ((apply (union %%hole%%2 %%hole%%5) x$)))))
; instantiations
;(assert (= (apply (union (intersection s1! s2!) (intersection s1! s3!)) a) (B (or (contains (intersection s1! s2!) a) (contains (intersection s1! s3!) a)))))



; also missing one from here
(assert (forall ((%%hole%%2 Poly)(%%hole%%5 Poly) (x$ Poly)) (! (= (apply (intersection %%hole%%2 %%hole%%5) x$) (B (and (contains %%hole%%2 x$) (contains %%hole%%5 x$)))) :pattern ((apply (intersection %%hole%%2 %%hole%%5) x$)))))
; instantiations
;(assert (= (apply (intersection s1! (union s2! s3!)) a) (B (and (contains s1! a) (contains (union s2! s3!) a)))))




; these are the assertions
; seems like we discover these assertions and also once we add them Sundance gets unsat,
; but still we are not unsat
;(assert (= (apply (union s2! s3!) a) (B (or (contains s2! a) (contains s3! a)))))
;(assert (= (apply (union (intersection s1! s2!) (intersection s1! s3!)) a) (B (or (contains (intersection s1! s2!) a) (contains (intersection s1! s3!) a)))))
;(assert (= (apply (intersection s1! s2!) a) (B (and (contains s1! a) (contains s2! a)))))
;(assert (= (apply (intersection s1! s3!) a) (B (and (contains s1! a) (contains s3! a)))))
;(assert (= (apply (intersection s1! (union s2! s3!)) a) (B (and (contains s1! a) (contains (union s2! s3!) a)))))

(assert (not (= (contains (intersection s1! (union s2! s3!)) a) 
                (contains (union (intersection s1! s2!) (intersection s1! s3!)) a))))


    

(declare-const %%location_label%%0 Bool)

; the assertions we get





(set-option :rlimit 30000000)
(check-sat)
(set-option :rlimit 0)
