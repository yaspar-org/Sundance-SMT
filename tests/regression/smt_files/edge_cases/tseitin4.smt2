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


(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%0 s2! s3!))) (%%lambda%%0 s2! s3!)))
(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)))) (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!))))
(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%1 s1! (union s2! s3!)))) (%%lambda%%1 s1! (union s2! s3!))))
(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%1 s1! s2!))) (%%lambda%%1 s1! s2!)))
(assert (= (%Poly%fun%1. (Poly%fun%1. (%%lambda%%1 s1! s3!))) (%%lambda%%1 s1! s3!)))



(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s2!)) a$skolem))) (%%apply%%0 (%Poly%fun%1. (intersection s1! s2!)) a$skolem)))
(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s3!)) a$skolem))) (%%apply%%0 (%Poly%fun%1. (intersection s1! s3!)) a$skolem)))
(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. s1!) a$skolem))) (%%apply%%0 (%Poly%fun%1. s1!) a$skolem)))
(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (union s2! s3!)) a$skolem))) (%%apply%%0 (%Poly%fun%1. (union s2! s3!)) a$skolem)))
(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! (union s2! s3!))) a$skolem))) (%%apply%%0 (%Poly%fun%1. (intersection s1! (union s2! s3!))) a$skolem)))
(assert (= (B (%B (%%apply%%0 (%Poly%fun%1. (union (intersection s1! s2!) (intersection s1! s3!))) a$skolem))) (%%apply%%0 (%Poly%fun%1. (union (intersection s1! s2!) (intersection s1! s3!))) a$skolem)))


(assert (= (contains (intersection s1! s2!) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s2!)) a$skolem))))
(assert (= (contains (intersection s1! s3!) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! s3!)) a$skolem))))
(assert (= (contains s1! a$skolem) (%B (%%apply%%0 (%Poly%fun%1. s1!) a$skolem))))
(assert (= (contains (union s2! s3!) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (union s2! s3!)) a$skolem))))
(assert (= (contains (intersection s1! (union s2! s3!)) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (intersection s1! (union s2! s3!))) a$skolem))))
(assert (= (contains (union (intersection s1! s2!) (intersection s1! s3!)) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (union (intersection s1! s2!) (intersection s1! s3!))) a$skolem))))



(assert (= (%%apply%%0 (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)) a$skolem) (B (or (contains (intersection s1! s2!) a$skolem) (contains (intersection s1! s3!) a$skolem)))))


(assert (= (union s2! s3!) (Poly%fun%1. (%%lambda%%0 s2! s3!))))
(assert (= (union (intersection s1! s2!) (intersection s1! s3!)) (Poly%fun%1. (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)))))




(assert (= (%%apply%%0 (%%lambda%%1 s1! (union s2! s3!)) a$skolem) (B (and (contains s1! a$skolem) (contains (union s2! s3!) a$skolem)))))



(assert (= (intersection s1! (union s2! s3!)) (Poly%fun%1. (%%lambda%%1 s1! (union s2! s3!)))))
(assert (= (intersection s1! s2!) (Poly%fun%1. (%%lambda%%1 s1! s2!))))
(assert (= (intersection s1! s3!) (Poly%fun%1. (%%lambda%%1 s1! s3!))))

; things added after commenting stuff out
; note that with these, z3 can produce a conflict, so we are instantiating correctly, there must be another problem
(assert (= (%%apply%%0 (%%lambda%%0 s2! s3!) a$skolem) (B (or (contains s2! a$skolem) (contains s3! a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%0 (intersection s1! s2!) (intersection s1! s3!)) a$skolem) (B (or (contains (intersection s1! s2!) a$skolem) (contains (intersection s1! s3!) a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 s1! s2!) a$skolem) (B (and (contains s1! a$skolem) (contains s2! a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 s1! s3!) a$skolem) (B (and (contains s1! a$skolem) (contains s3! a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 s1! (union s2! s3!)) a$skolem) (B (and (contains s1! a$skolem) (contains (union s2! s3!) a$skolem)))))


(assert (not (= (contains (intersection s1! (union s2! s3!)) a$skolem) 
                (contains (union (intersection s1! s2!) (intersection s1! s3!)) a$skolem))))


    

(declare-const %%location_label%%0 Bool)

; the assertions we get






(set-option :rlimit 30000000)
(check-sat)
(set-option :rlimit 0)
