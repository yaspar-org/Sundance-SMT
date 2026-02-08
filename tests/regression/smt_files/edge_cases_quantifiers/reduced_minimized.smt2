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
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
(declare-fun contains (Poly Poly) Bool)
(declare-fun union (Poly Poly) Poly)
(declare-fun intersection (Poly Poly) Poly)
(declare-const s1! Poly)
(declare-const s2! Poly)
(declare-const s3! Poly)

(declare-fun %%lambda%%0 (Poly Poly) %%Function%%)
(declare-fun %%lambda%%1 (Poly Poly) %%Function%%)




(declare-const a$skolem Poly)

(assert (forall ((x %%Function%%)) (! (= (%Poly%fun%1. (Poly%fun%1. x)) x) :pattern ((Poly%fun%1. x)) )))
; instantiations
;(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%0 s2! s3!))) (%%lambda%%0 s2! s3!)))
;(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)))) (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!))))
;(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%1 s1! (union s2! s3!)))) (%%lambda%%1 s1! (union s2! s3!))))
;(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%1 s1! s2!))) (%%lambda%%1 s1! s2!)))
;(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%1 s1! s3!))) (%%lambda%%1 s1! s3!)))


(assert (forall ((x Poly)) (! (= (B (%B x)) x) :pattern ((%B x)) )))
; instantiations
;(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s2!)) a$skolem))) (%%apply%%0 (%Poly%fun%1. (intersection s1! s2!)) a$skolem)))
;(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s3!)) a$skolem))) (%%apply%%0 (%Poly%fun%1. (intersection s1! s3!)) a$skolem)))
;(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. s1!) a$skolem))) (%%apply%%0 (%Poly%fun%1. s1!) a$skolem)))
;(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (union s2! s3!)) a$skolem))) (%%apply%%0 (%Poly%fun%1. (union s2! s3!)) a$skolem)))
;(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! (union s2! s3!))) a$skolem))) (%%apply%%0 (%Poly%fun%1. (intersection s1! (union s2! s3!))) a$skolem)))
;(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (union (intersection s1! s2!) (intersection s1! s3!))) a$skolem))) (%%apply%%0 (%Poly%fun%1. (union (intersection s1! s2!) (intersection s1! s3!))) a$skolem)))


; note we need this contains even with 
(assert (forall ((f! Poly) (a! Poly)) (!  (= (contains f! a!) (%B (%%apply%%0 (%Poly%fun%1. f!) a!))) :pattern ((contains f! a!)) )))
; instantiations
;(assert (= (contains (intersection s1! s2!) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s2!)) a$skolem))))
;(assert (= (contains (intersection s1! s3!) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s3!)) a$skolem))))
;(assert (= (contains s1! a$skolem) (%B (%%apply%%0 (%Poly%fun%1. s1!) a$skolem))))
;(assert (= (contains (union s2! s3!) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (union s2! s3!)) a$skolem))))
;(assert (= (contains (intersection s1! (union s2! s3!)) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! (union s2! s3!))) a$skolem))))
;(assert (= (contains (union (intersection s1! s2!) (intersection s1! s3!)) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (union (intersection s1! s2!) (intersection s1! s3!))) a$skolem))))


; I think we are missing one of these
(assert (forall ((%%hole%%2 Poly)(%%hole%%5 Poly) (x$ Poly)) (! (= (%%apply%%0 (%%lambda%%0 %%hole%%2 %%hole%%5) x$) (B (or (contains %%hole%%2 x$) (contains %%hole%%5 x$)))) :pattern ((%%apply%%0 (%%lambda%%0 %%hole%%2 %%hole%%5) x$)))))
; instantiations
;(assert (= (%%apply%%0 (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)) a$skolem) (B (or (contains (intersection s1! s2!) a$skolem) (contains (intersection s1! s3!) a$skolem)))))

(assert (forall ((s1! Poly) (s2! Poly)) (! (= (union s1! s2!) (Poly%fun%1. (%%lambda%%0 s1! s2!))) :pattern ((union s1! s2!)) )))
; instantiations
;(assert (= (union s2! s3!) (Poly%fun%1. (%%lambda%%0 s2! s3!))))
;(assert (= (union (intersection s1! s2!) (intersection s1! s3!)) (Poly%fun%1. (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)))))



; also missing one from here
(assert (forall ((%%hole%%2 Poly)(%%hole%%5 Poly) (x$ Poly)) (! (= (%%apply%%0 (%%lambda%%1 %%hole%%2 %%hole%%5) x$) (B (and (contains %%hole%%2 x$) (contains %%hole%%5 x$)))) :pattern ((%%apply%%0 (%%lambda%%1 %%hole%%2 %%hole%%5) x$)))))
; instantiations
;(assert (= (%%apply%%0 (%%lambda%%1 s1! (union s2! s3!)) a$skolem) (B (and (contains s1! a$skolem) (contains (union s2! s3!) a$skolem)))))


(assert (forall ((s1! Poly) (s2! Poly)) (! (= (intersection s1! s2!) (Poly%fun%1. (%%lambda%%1 s1! s2!))) :pattern ((intersection s1! s2!)) )))
; instantiations
;(assert (= (intersection s1! (union s2! s3!)) (Poly%fun%1. (%%lambda%%1 s1! (union s2! s3!)))))
;(assert (= (intersection s1! s2!) (Poly%fun%1. (%%lambda%%1 s1! s2!))))
;(assert (= (intersection s1! s3!) (Poly%fun%1. (%%lambda%%1 s1! s3!))))

; these are the assertions
; seems like we discover these assertions and also once we add them Sundance gets unsat,
; but still we are not unsat
(assert (= (%%apply%%0 (%%lambda%%0 s2! s3!) a$skolem) (B (or (contains s2! a$skolem) (contains s3! a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)) a$skolem) (B (or (contains (intersection s1! s2!) a$skolem) (contains (intersection s1! s3!) a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 s1! s2!) a$skolem) (B (and (contains s1! a$skolem) (contains s2! a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 s1! s3!) a$skolem) (B (and (contains s1! a$skolem) (contains s3! a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 s1! (union s2! s3!)) a$skolem) (B (and (contains s1! a$skolem) (contains (union s2! s3!) a$skolem)))))

; things added after commenting stuff out
; originally not producing a conflict with these but now we are
;(assert (= (%%apply%%0 (%%lambda%%0 s2! s3!) a$skolem) (B (or (contains s2! a$skolem) (contains s3! a$skolem)))))
;(assert (= (%%apply%%0 (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)) a$skolem) (B (or (contains (intersection s1! s2!) a$skolem) (contains (intersection s1! s3!) a$skolem)))))
;(assert (= (%%apply%%0 (%%lambda%%1 s1! s2!) a$skolem) (B (and (contains s1! a$skolem) (contains s2! a$skolem)))))
;(assert (= (%%apply%%0 (%%lambda%%1 s1! s3!) a$skolem) (B (and (contains s1! a$skolem) (contains s3! a$skolem)))))
;(assert (= (%%apply%%0 (%%lambda%%1 s1! (union s2! s3!)) a$skolem) (B (and (contains s1! a$skolem) (contains (union s2! s3!) a$skolem)))))


(assert (not (= (contains (intersection s1! (union s2! s3!)) a$skolem) 
                (contains (union (intersection s1! s2!) (intersection s1! s3!)) a$skolem))))


    

(declare-const %%location_label%%0 Bool)

; the assertions we get






(set-option :rlimit 30000000)
(check-sat)
(set-option :rlimit 0)
