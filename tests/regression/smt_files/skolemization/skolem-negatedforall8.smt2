(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    
    
))))
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun F (fndef) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %F (Poly) fndef)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const CHAR Type)
(declare-const USIZE Type)
(declare-const ISIZE Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-fun CONST_BOOL (Bool) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-const $slice Dcr)
(declare-fun DST (Dcr) Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr Type Dcr) Dcr)
(declare-fun RC (Dcr Type Dcr) Dcr)
(declare-fun ARC (Dcr Type Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun CONST_PTR (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-const STRSLICE Type)
(declare-const ALLOCATOR_GLOBAL Type)
(declare-fun PTR (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun sized (Dcr) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(declare-fun const_bool (Type) Bool)
(assert
 (sized $)
)

;necessary
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   
   
)))

;necessary
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   
   
)))



;necessary
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   
   
)))

(declare-fun ext_eq (Bool Type Poly Poly) Bool)

(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)

(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(declare-fun charClip (Int) Int)



(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(declare-fun charInv (Int) Bool)







;; MODULE 'root module'

;; Fuel
(declare-const fuel%vstd!set.axiom_set_new. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal_deep. FuelId)
(declare-const fuel%set_membership!is_member. FuelId)
(declare-const fuel%set_membership!set_union. FuelId)
(declare-const fuel%set_membership!set_intersection. FuelId)
(declare-const fuel%set_membership!set_difference. FuelId)
(declare-const fuel%vstd!array.group_array_axioms. FuelId)
(declare-const fuel%vstd!function.group_function_axioms. FuelId)
(declare-const fuel%vstd!layout.group_layout_axioms. FuelId)
(declare-const fuel%vstd!map.group_map_axioms. FuelId)
(declare-const fuel%vstd!multiset.group_multiset_axioms. FuelId)
(declare-const fuel%vstd!raw_ptr.group_raw_ptr_axioms. FuelId)
(declare-const fuel%vstd!seq.group_seq_axioms. FuelId)
(declare-const fuel%vstd!seq_lib.group_filter_ensures. FuelId)
(declare-const fuel%vstd!seq_lib.group_seq_lib_default. FuelId)
(declare-const fuel%vstd!set.group_set_axioms. FuelId)
(declare-const fuel%vstd!set_lib.group_set_lib_default. FuelId)
(declare-const fuel%vstd!slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!string.group_string_axioms. FuelId)
(declare-const fuel%vstd!std_specs.bits.group_bits_axioms. FuelId)
(declare-const fuel%vstd!std_specs.control_flow.group_control_flow_axioms. FuelId)
(declare-const fuel%vstd!std_specs.hash.group_hash_axioms. FuelId)
(declare-const fuel%vstd!std_specs.range.group_range_axioms. FuelId)
(declare-const fuel%vstd!std_specs.slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vec.group_vec_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms. FuelId)
(declare-const fuel%vstd!group_vstd_default. FuelId)

(assert
 (=>
  (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
  (fuel_bool_default fuel%vstd!seq_lib.group_filter_ensures.)
))
(assert
 (=>
  (fuel_bool_default fuel%vstd!set.group_set_axioms.)
  (and
   (fuel_bool_default fuel%vstd!set.axiom_set_new.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal_deep.)
)))
(assert
 (fuel_bool_default fuel%vstd!group_vstd_default.)
)
(assert
 (=>
  (fuel_bool_default fuel%vstd!group_vstd_default.)
  (and
   (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
   (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
   (fuel_bool_default fuel%vstd!map.group_map_axioms.)
   (fuel_bool_default fuel%vstd!set.group_set_axioms.)
   (fuel_bool_default fuel%vstd!set_lib.group_set_lib_default.)
   (fuel_bool_default fuel%vstd!std_specs.bits.group_bits_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.control_flow.group_control_flow_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vec.group_vec_axioms.)
   (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!array.group_array_axioms.)
   (fuel_bool_default fuel%vstd!multiset.group_multiset_axioms.)
   (fuel_bool_default fuel%vstd!string.group_string_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.range.group_range_axioms.)
   (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
   (fuel_bool_default fuel%vstd!layout.group_layout_axioms.)
   (fuel_bool_default fuel%vstd!function.group_function_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.hash.group_hash_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.slice.group_slice_axioms.)
)))

;; Datatypes
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-fun TYPE%fun%1. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
;necessary
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%fun%1. (Poly%fun%1. x)))
   :pattern ((Poly%fun%1. x))
   
   
)))

(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
;necessary
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x %%Function%%)) (!
   (=>
    (forall ((T%0 Poly)) (!
      (=>
       (has_type T%0 T%0&)
       (has_type (%%apply%%0 x T%0) T%1&)
      )
      :pattern ((has_type (%%apply%%0 x T%0) T%1&))
      
      
    ))
    (has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
   )
   :pattern ((has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   
   
)))



;; Function-Decl vstd::set::Set::contains
(declare-fun vstd!set.Set.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::set::impl&%0::new
(declare-fun vstd!set.impl&%0.new.? (Dcr Type Poly) Poly)

;; Function-Decl set_membership::is_member
(declare-fun set_membership!is_member.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_membership::set_union
(declare-fun set_membership!set_union.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_membership::set_intersection
(declare-fun set_membership!set_intersection.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_membership::set_difference
(declare-fun set_membership!set_difference.? (Dcr Type Poly Poly) Poly)



;; Broadcast vstd::set::axiom_set_new
;necessary
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_new.)
  (forall ((A&. Dcr) (A& Type) (f! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type f! (TYPE%fun%1. A&. A& $ BOOL))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (= (vstd!set.Set.contains.? A&. A& (vstd!set.impl&%0.new.? A&. A& f!) a!) (%B (%%apply%%0
         (%Poly%fun%1. f!) a!
    )))))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.impl&%0.new.? A&. A& f!) a!))
    
    
))))

;; Broadcast vstd::set::axiom_set_ext_equal
;necessary
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_ext_equal.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!) (forall ((a$ Poly)) (!
         (=>
          (has_type a$ A&)
          (= (vstd!set.Set.contains.? A&. A& s1! a$) (vstd!set.Set.contains.? A&. A& s2! a$))
         )
         :pattern ((vstd!set.Set.contains.? A&. A& s1! a$))
         :pattern ((vstd!set.Set.contains.? A&. A& s2! a$))
         
         
    )))))
    :pattern ((ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!))
    
    
))))

;; Broadcast vstd::set::axiom_set_ext_equal_deep


;; Function-Axioms set_membership::is_member


;; Function-Axioms set_membership::set_union
(assert
 (fuel_bool_default fuel%set_membership!set_union.)
)
(declare-fun %%lambda%%0 (Dcr Type Poly Dcr Type Poly) %%Function%%)
;necessary
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 Dcr) (%%hole%%4
    Type
   ) (%%hole%%5 Poly) (x$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5)
     x$
    ) (B (or
      (vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 x$)
      (vstd!set.Set.contains.? %%hole%%3 %%hole%%4 %%hole%%5 x$)
   )))
   :pattern ((%%apply%%0 (%%lambda%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5
     ) x$
)))))
;necessary
(assert
 (=>
  (fuel_bool fuel%set_membership!set_union.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_membership!set_union.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%0 T&. T& s1! T&. T& s2!))
    )))
    :pattern ((set_membership!set_union.? T&. T& s1! s2!))
    
    
))))
;necessary
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_membership!set_union.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_membership!set_union.? T&. T& s1! s2!))
   
   
)))

;; Function-Axioms set_membership::set_intersection
(assert
 (fuel_bool_default fuel%set_membership!set_intersection.)
)
(declare-fun %%lambda%%1 (Dcr Type Poly Dcr Type Poly) %%Function%%)

(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 Dcr) (%%hole%%4
    Type
   ) (%%hole%%5 Poly) (x$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%1 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5)
     x$
    ) (B (and
      (vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 x$)
      (vstd!set.Set.contains.? %%hole%%3 %%hole%%4 %%hole%%5 x$)
   )))
   :pattern ((%%apply%%0 (%%lambda%%1 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5
     ) x$
)))))
(assert
 (=>
  (fuel_bool fuel%set_membership!set_intersection.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_membership!set_intersection.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T&
      (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)))
    ))
    :pattern ((set_membership!set_intersection.? T&. T& s1! s2!))
    
    
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_membership!set_intersection.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&.
      T&
   )))
   :pattern ((set_membership!set_intersection.? T&. T& s1! s2!))
   
   
)))

;; Function-Axioms set_membership::set_difference
(assert
 (fuel_bool_default fuel%set_membership!set_difference.)
)
(declare-fun %%lambda%%2 (Dcr Type Poly Dcr Type Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 Dcr) (%%hole%%4
    Type
   ) (%%hole%%5 Poly) (x$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%2 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5)
     x$
    ) (B (and
      (vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 x$)
      (not (vstd!set.Set.contains.? %%hole%%3 %%hole%%4 %%hole%%5 x$))
   )))
   :pattern ((%%apply%%0 (%%lambda%%2 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5
     ) x$
)))))
(assert
 (=>
  (fuel_bool fuel%set_membership!set_difference.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_membership!set_difference.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T&
      (Poly%fun%1. (mk_fun (%%lambda%%2 T&. T& s1! T&. T& s2!)))
    ))
    :pattern ((set_membership!set_difference.? T&. T& s1! s2!))
    
    
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_membership!set_difference.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&.
      T&
   )))
   :pattern ((set_membership!set_difference.? T&. T& s1! s2!))
   
   
)))

;; Function-Specs set_membership::union_membership_lemma
(declare-fun ens%set_membership!union_membership_lemma. (Dcr Type Poly Poly Poly)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly) (s1! Poly) (s2! Poly)) (!
   (= (ens%set_membership!union_membership_lemma. T&. T& x! s1! s2!) (=>
     (and
      (set_membership!is_member.? T&. T& x! (set_membership!set_union.? T&. T& s1! s2!))
      (not (set_membership!is_member.? T&. T& x! s1!))
     )
     (set_membership!is_member.? T&. T& x! s2!)
   ))
   :pattern ((ens%set_membership!union_membership_lemma. T&. T& x! s1! s2!))
   
   
)))

;; Function-Def set_membership::union_membership_lemma
;; set_membership.rs:17:7: 17:65 (#0)

 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const s1! Poly)
 (declare-const s2! Poly)
 (declare-const s3! Poly)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type s1! (TYPE%vstd!set.Set. T&. T&))
 )
 (assert
  (has_type s2! (TYPE%vstd!set.Set. T&. T&))
 )
 (assert
  (has_type s3! (TYPE%vstd!set.Set. T&. T&))
 )
 ;; postcondition not satisfied
 (declare-const %%location_label%%0 Bool)
 (assert
  (not (=>
    %%location_label%%0
    (ext_eq false (TYPE%vstd!set.Set. T&. T&) (set_membership!set_intersection.? T&. T&
      s1! (set_membership!set_union.? T&. T& s2! s3!)
     ) (set_membership!set_union.? T&. T& (set_membership!set_intersection.? T&. T& s1!
       s2!
      ) (set_membership!set_intersection.? T&. T& s1! s3!)
 )))))
 
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
