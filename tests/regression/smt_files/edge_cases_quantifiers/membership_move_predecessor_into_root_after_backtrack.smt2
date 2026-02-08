(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)

(declare-sort % 0)
(declare-sort Poly 0)
(declare-fun B (Bool) Poly)
(declare-fun %B (Poly) Bool)
(declare-sort T 0)
(declare-const BOOL T)
(declare-sort D 0)
(declare-const $ D)
(declare-fun has_type (Poly T) Bool)
(declare-fun sized (D) Bool)
(declare-fun mk_fun (%) %)





(declare-fun TYPE%fun%1. (D T D T) T)
(declare-fun Poly%fun%1. (%) Poly)
(declare-fun %Poly%fun%1. (Poly) %)
(declare-fun %%apply%%0 (% Poly) Poly)
(declare-fun vstd!set.Set.contains.? (D T Poly Poly) Bool)
(declare-fun vstd!set.impl&%0.new.? (D T Poly) Poly)
(declare-fun set_membership!set_union.? (D T Poly Poly) Poly)
(declare-fun set_membership!set_intersection.? (D T Poly Poly) Poly)
(declare-fun %%lambda%%0 (D T Poly D T Poly) %)
(declare-fun %%lambda%%1 (D T Poly D T Poly) %)
(declare-const T&. D)
(declare-const T& T)
(declare-const s1! Poly)
(declare-const s2! Poly)
(declare-const s3! Poly)

(declare-const !!skolem_variable_0 Poly)
(declare-const !!skolem_variable_1 Poly)
(declare-const !!skolem_variable_2 Poly)
(declare-const !!skolem_variable_3 Poly)
(declare-const !!skolem_variable_4 Poly)

;(assert (forall ((T D) (% T) (T% D) (%1 T) (x %)) (! (=> (forall ((T%0 Poly)) (! (=> (has_type T%0 %) (has_type (%%apply%%0 x T%0) BOOL)) :pattern ((has_type (%%apply%%0 x T%0) BOOL)))) (has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T % T% BOOL))) :pattern ((has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T % T% %1))))))

;instantiations of this guy
(assert (=> (=> (has_type !!skolem_variable_0 T&) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0) BOOL))
          (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)))) (TYPE%fun%1. T&. T& $ BOOL))))
(assert (=> (=> (has_type !!skolem_variable_1 T&) (has_type (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1) BOOL)) 
               (has_type (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)))) (TYPE%fun%1. T&. T& $ BOOL))))
(assert (=> (=> (has_type !!skolem_variable_2 T&) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2) BOOL))
           (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!))) (TYPE%fun%1. T&. T& $ BOOL))))
(assert (=> (=> (has_type !!skolem_variable_3 T&) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3) BOOL))
           (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!))) (TYPE%fun%1. T&. T& $ BOOL))))
(assert (=> (=> (has_type !!skolem_variable_4 T&) (has_type (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4) BOOL))
            (has_type (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!))) (TYPE%fun%1. T&. T& $ BOOL))))




(assert (sized T&.))
(declare-const a$skolem Poly)
(assert (has_type a$skolem T&))
(assert (not (= (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! (set_membership!set_union.? T&. T& s2! s3!)) a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_union.? T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) (set_membership!set_intersection.? T&. T& s1! s3!)) a$skolem))))

(assert (forall ((b Bool)) (! (has_type (B b) BOOL) :pattern ((B b)))))
; instantiation -> missing stuff
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4))) BOOL))
; these are not enough instantiations!!! -> idk what is tho
;(assert (has_type (B (or (vstd!set.Set.contains.? T&. T& s2! !!skolem_variable_4) (vstd!set.Set.contains.? T&. T& s3! !!skolem_variable_4))) BOOL))
;(assert (has_type (B (or (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! s3!) a$skolem))) BOOL))
;(assert (has_type (B (or (vstd!set.Set.contains.? T&. T& s2! a$skolem) (vstd!set.Set.contains.? T&. T& s3! a$skolem))) BOOL))
;(assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_union.? T&. T& s2! s3!) a$skolem))) BOOL))
;(assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s2! a$skolem))) BOOL))
;(assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s3! a$skolem))) BOOL))

; these are teh instanatiations z3 uses in its proof
; if we give these same instantiations to sundance it solves it too, but we do need the other quantifier
; meaning we are probably missing on these instantiations
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3))) BOOL))
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2))) BOOL))
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1))) BOOL))
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0))) BOOL))


; tranlste these to z3 instantiations to see if they could have come from the other quantiger
; ok I think these happened first, so need to see why sundance cannot discover these -> actually I have no idea which order these are supposed to happen
; wait these are supposed to trigger first because of above -> why are they not being found??
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3)))))
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2)))))
;(assert (= (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1) (B (%B (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1)))))
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0)))))

; adding reflexive equalities for each of these to match patterns
;(assert (= (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3) BOOL) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3) BOOL)))
;(assert (= (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2) BOOL) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2) BOOL)))
;(assert (= (has_type (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1) BOOL) (has_type (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1) BOOL)))
;(assert (= (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0) BOOL) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0) BOOL)))

; these are the instantiations sundance discovers
;(assert (has_type (B (or (vstd!set.Set.contains.? T&. T& s2! !!skolem_variable_4) (vstd!set.Set.contains.? T&. T& s3! !!skolem_variable_4))) BOOL))
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0)))))
;(assert (= (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1) (B (%B (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1)))))
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2)))))
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3)))))
;(assert (= (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4) (B (%B (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4)))))
;(assert (has_type (B (or (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! s3!) a$skolem))) BOOL))


; instantiations sundance discovers once you give it the above instantiations -> but it should use current instantiations to discover new instantiations, why doesnt it do this??
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0))) BOOL))
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1))) BOOL))
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2))) BOOL))
;(assert (has_type (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3))) BOOL))


; note that the two below are sufficient enough to cover the 4 above cases
;(assert (has_type (B true) BOOL))
;(assert (has_type (B false) BOOL))


;(assert (forall ((x %)) (! (= (mk_fun x) x) :pattern ((mk_fun x)))))
; instantiations -> works
(assert (= (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!)) (%%lambda%%0 T&. T& s2! T&. T& s3!)))
(assert (= (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!))) (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!))))
(assert (= (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!))) (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!))))
(assert (= (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)) (%%lambda%%1 T&. T& s1! T&. T& s2!)))
(assert (= (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!)) (%%lambda%%1 T&. T& s1! T&. T& s3!)))


(assert (forall ((x Poly)) (! (= x (B (%B x))) :pattern ((has_type x BOOL)))))
; instantiations -> missing stuff
;(assert (= (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4) (B (%B (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4)))))
;(assert (= (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4) (B (%B (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4)))))

; instantiations somehow now work -> but when you give all of these, sundance can actually solve it
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0)))))
;(assert (= (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1) (B (%B (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1)))))
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2)))))
;(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3) (B (%B (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3)))))
;(assert (= (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4) (B (%B (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4)))))

;(assert (forall ((x %)) (! (= x (%Poly%fun%1. (Poly%fun%1. x))) :pattern ((Poly%fun%1. x)))))
; instantiations -> works
(assert (= (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!)) (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!))))))
(assert (= (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!))) (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)))))))
(assert (= (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!))) (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)))))))
(assert (= (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)) (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!))))))
(assert (= (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!)) (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!))))))


;(assert (forall ((& D) (A T) (f Poly) (a Poly)) (! (=> (and (has_type f (TYPE%fun%1. & A $ BOOL)) (has_type a A)) (=> (sized &) (= (vstd!set.Set.contains.? & A (vstd!set.impl&%0.new.? & A f) a) (%B (%%apply%%0 (%Poly%fun%1. f) a))))) :pattern ((vstd!set.Set.contains.? & A (vstd!set.impl&%0.new.? & A f) a)))))
; instantiations
(assert (=> (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)))) (TYPE%fun%1. T&. T& $ BOOL)) (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!))))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!))))) a$skolem))))))
(assert (=> (has_type (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)))) (TYPE%fun%1. T&. T& $ BOOL)) (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!))))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!))))) a$skolem))))))
(assert (=> (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!))) (TYPE%fun%1. T&. T& $ BOOL)) (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)))) a$skolem))))))
(assert (=> (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!))) (TYPE%fun%1. T&. T& $ BOOL)) (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!)))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!)))) a$skolem))))))
(assert (=> (has_type (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!))) (TYPE%fun%1. T&. T& $ BOOL)) (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!)))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!)))) a$skolem))))))


; experimental non has_type version of the above 
; note that with these we dont need the type quantifer
; hence the type quantifier is useful for instantiating the avoe guys
;(assert (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!))))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!))))) a$skolem)))))
;(assert (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!))))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!))))) a$skolem)))))
;(assert (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)))) a$skolem)))))
;(assert (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!)))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!)))) a$skolem)))))
;(assert (=> (sized T&.) (= (vstd!set.Set.contains.? T&. T& (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!)))) a$skolem) (%B (%%apply%%0 (%Poly%fun%1. (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!)))) a$skolem)))))




;(assert (forall ((% D) (%% T) (h Poly) (%h D) (%%h T) (o Poly) (x Poly)) (! (= (%%apply%%0 (%%lambda%%0 %h %%h h %h %%h o) x) (B (or (vstd!set.Set.contains.? %h %%h h x) (vstd!set.Set.contains.? %h %%h o x)))) :pattern ((%%apply%%0 (%%lambda%%0 % %% h %h %%h o) x)))))
; instantiations
(assert (= (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4) (B (or (vstd!set.Set.contains.? T&. T& s2! !!skolem_variable_4) (vstd!set.Set.contains.? T&. T& s3! !!skolem_variable_4)))))
(assert (= (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) a$skolem) (B (or (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! s3!) a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) a$skolem) (B (or (vstd!set.Set.contains.? T&. T& s2! a$skolem) (vstd!set.Set.contains.? T&. T& s3! a$skolem)))))

;(assert (forall ((T&. D) (T& T) (s1! Poly) (s2! Poly)) (! (= (set_membership!set_union.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s1! T&. T& s2!))))) :pattern ((set_membership!set_union.? T&. T& s1! s2!)))))
; instantiations
(assert (= (set_membership!set_union.? T&. T& s2! s3!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!))))))
(assert (= (set_membership!set_union.? T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) (set_membership!set_intersection.? T&. T& s1! s3!)) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)))))))

;(assert (forall ((% D) (%% T) (h Poly) (%h D) (%%h T) (o Poly) (x Poly)) (! (= (%%apply%%0 (%%lambda%%1 %h %%h h %h %%h o) x) (B (and (vstd!set.Set.contains.? %h %%h h x) (vstd!set.Set.contains.? %h %%h o x)))) :pattern ((%%apply%%0 (%%lambda%%1 % %% h %h %%h o) x)))))
; instantiations
(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) a$skolem) (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_union.? T&. T& s2! s3!) a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) a$skolem) (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s2! a$skolem)))))
(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) a$skolem) (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s3! a$skolem)))))

;(assert (forall ((T&. D) (T& T) (s1! Poly) (s2! Poly)) (! (= (set_membership!set_intersection.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!))))) :pattern ((set_membership!set_intersection.? T&. T& s1! s2!)))))
;instantiations
(assert (= (set_membership!set_intersection.? T&. T& s1! (set_membership!set_union.? T&. T& s2! s3!)) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)))))))
(assert (= (set_membership!set_intersection.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!))))))
(assert (= (set_membership!set_intersection.? T&. T& s1! s3!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!))))))

(check-sat)
