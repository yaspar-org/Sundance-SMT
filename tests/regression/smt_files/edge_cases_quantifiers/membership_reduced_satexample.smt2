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
;(assert (=> (=> (has_type !!skolem_variable_0 T&) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) !!skolem_variable_0) BOOL))
;           (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)))) (TYPE%fun%1. T&. T& $ BOOL))))
;(assert (=> (=> (has_type !!skolem_variable_1 T&) (has_type (%%apply%%0 (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)) !!skolem_variable_1) BOOL)) 
 ;               (has_type (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) T&. T& (set_membership!set_intersection.? T&. T& s1! s3!)))) (TYPE%fun%1. T&. T& $ BOOL))))
;(assert (=> (=> (has_type !!skolem_variable_2 T&) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) !!skolem_variable_2) BOOL))
;            (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!))) (TYPE%fun%1. T&. T& $ BOOL))))
;(assert (=> (=> (has_type !!skolem_variable_3 T&) (has_type (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) !!skolem_variable_3) BOOL))
;            (has_type (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s3!))) (TYPE%fun%1. T&. T& $ BOOL))))
(assert (=> (=> (has_type !!skolem_variable_4 T&) (has_type (%%apply%%0 (%%lambda%%0 T&. T& s2! T&. T& s3!) !!skolem_variable_4) BOOL))
            (has_type (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& s2! T&. T& s3!))) (TYPE%fun%1. T&. T& $ BOOL))))




(assert (sized T&.))
(declare-const a$skolem Poly)
(assert (has_type a$skolem T&))
(assert (not (= (vstd!set.Set.contains.? T&. T& (set_membership!set_intersection.? T&. T& s1! (set_membership!set_union.? T&. T& s2! s3!)) a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_union.? T&. T& (set_membership!set_intersection.? T&. T& s1! s2!) (set_membership!set_intersection.? T&. T& s1! s3!)) a$skolem))))

; getting only one instantiation even though three B (and)
(declare-const t1 Bool)
(declare-const t2 Bool)
(assert (forall ((b Bool)) (! (has_type (B b) BOOL) :pattern ((B b)))))
;(assert (= (B true) (B true)))
;(assert (= (B false) (B false)))
;(assert (or (not (has_type (B t1) BOOL)) (not (has_type (B t2) BOOL)) (not (has_type (B (and t1 t2)) BOOL))))
;(assert (= (B (and t1 t2)) (B (and t2 t1))))

(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s2!) a$skolem) (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s2! a$skolem)))))
; instantiation -> (assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s2! a$skolem))) BOOL))
(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& s3!) a$skolem) (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s3! a$skolem)))))
; (assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s3! a$skolem))) BOOL))
(assert (= (%%apply%%0 (%%lambda%%1 T&. T& s1! T&. T& (set_membership!set_union.? T&. T& s2! s3!)) a$skolem) (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_union.? T&. T& s2! s3!) a$skolem)))))

; notice we are only getting these instantiations one at a time
;(assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s2! a$skolem))) BOOL))
;(assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& s3! a$skolem))) BOOL))
;(assert (has_type (B (and (vstd!set.Set.contains.? T&. T& s1! a$skolem) (vstd!set.Set.contains.? T&. T& (set_membership!set_union.? T&. T& s2! s3!) a$skolem))) BOOL))
(check-sat)
