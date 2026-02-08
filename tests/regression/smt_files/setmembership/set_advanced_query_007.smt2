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
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
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
 (forall ((d Dcr)) (!
   (=>
    (sized d)
    (sized (DST d))
   )
   :pattern ((sized (DST d)))
   :qid prelude_sized_decorate_struct_inherit
   :skolemid skolem_prelude_sized_decorate_struct_inherit
)))
(assert
 (forall ((d Dcr)) (!
   (sized (REF d))
   :pattern ((sized (REF d)))
   :qid prelude_sized_decorate_ref
   :skolemid skolem_prelude_sized_decorate_ref
)))
(assert
 (forall ((d Dcr)) (!
   (sized (MUT_REF d))
   :pattern ((sized (MUT_REF d)))
   :qid prelude_sized_decorate_mut_ref
   :skolemid skolem_prelude_sized_decorate_mut_ref
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (BOX d t d2))
   :pattern ((sized (BOX d t d2)))
   :qid prelude_sized_decorate_box
   :skolemid skolem_prelude_sized_decorate_box
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (RC d t d2))
   :pattern ((sized (RC d t d2)))
   :qid prelude_sized_decorate_rc
   :skolemid skolem_prelude_sized_decorate_rc
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (ARC d t d2))
   :pattern ((sized (ARC d t d2)))
   :qid prelude_sized_decorate_arc
   :skolemid skolem_prelude_sized_decorate_arc
)))
(assert
 (forall ((d Dcr)) (!
   (sized (GHOST d))
   :pattern ((sized (GHOST d)))
   :qid prelude_sized_decorate_ghost
   :skolemid skolem_prelude_sized_decorate_ghost
)))
(assert
 (forall ((d Dcr)) (!
   (sized (TRACKED d))
   :pattern ((sized (TRACKED d)))
   :qid prelude_sized_decorate_tracked
   :skolemid skolem_prelude_sized_decorate_tracked
)))
(assert
 (forall ((d Dcr)) (!
   (sized (NEVER d))
   :pattern ((sized (NEVER d)))
   :qid prelude_sized_decorate_never
   :skolemid skolem_prelude_sized_decorate_never
)))
(assert
 (forall ((d Dcr)) (!
   (sized (CONST_PTR d))
   :pattern ((sized (CONST_PTR d)))
   :qid prelude_sized_decorate_const_ptr
   :skolemid skolem_prelude_sized_decorate_const_ptr
)))
(assert
 (sized $)
)
(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
   :skolemid skolem_prelude_type_id_const_int
)))
(assert
 (forall ((b Bool)) (!
   (= b (const_bool (CONST_BOOL b)))
   :pattern ((CONST_BOOL b))
   :qid prelude_type_id_const_bool
   :skolemid skolem_prelude_type_id_const_bool
)))
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
   :skolemid skolem_prelude_has_type_bool
)))
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x USIZE)
    (= x (I (%I x)))
   )
   :pattern ((has_type x USIZE))
   :qid prelude_box_unbox_usize
   :skolemid skolem_prelude_box_unbox_usize
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x ISIZE)
    (= x (I (%I x)))
   )
   :pattern ((has_type x ISIZE))
   :qid prelude_box_unbox_isize
   :skolemid skolem_prelude_box_unbox_isize
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (I (%I x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(declare-fun charClip (Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(assert
 (forall ((i Int)) (!
   (and
    (or
     (and
      (<= 0 (charClip i))
      (<= (charClip i) 55295)
     )
     (and
      (<= 57344 (charClip i))
      (<= (charClip i) 1114111)
    ))
    (=>
     (or
      (and
       (<= 0 i)
       (<= i 55295)
      )
      (and
       (<= 57344 i)
       (<= i 1114111)
     ))
     (= i (charClip i))
   ))
   :pattern ((charClip i))
   :qid prelude_char_clip
   :skolemid skolem_prelude_char_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(declare-fun charInv (Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((i Int)) (!
   (= (charInv i) (or
     (and
      (<= 0 i)
      (<= i 55295)
     )
     (and
      (<= 57344 i)
      (<= i 1114111)
   )))
   :pattern ((charInv i))
   :qid prelude_char_inv
   :skolemid skolem_prelude_char_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((x Int)) (!
   (=>
    (uInv SZ x)
    (has_type (I x) USIZE)
   )
   :pattern ((has_type (I x) USIZE))
   :qid prelude_has_type_usize
   :skolemid skolem_prelude_has_type_usize
)))
(assert
 (forall ((x Int)) (!
   (=>
    (iInv SZ x)
    (has_type (I x) ISIZE)
   )
   :pattern ((has_type (I x) ISIZE))
   :qid prelude_has_type_isize
   :skolemid skolem_prelude_has_type_isize
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Int)) (!
   (=>
    (charInv x)
    (has_type (I x) CHAR)
   )
   :pattern ((has_type (I x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x USIZE)
    (uInv SZ (%I x))
   )
   :pattern ((has_type x USIZE))
   :qid prelude_unbox_usize
   :skolemid skolem_prelude_unbox_usize
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x ISIZE)
    (iInv SZ (%I x))
   )
   :pattern ((has_type x ISIZE))
   :qid prelude_unbox_isize
   :skolemid skolem_prelude_unbox_isize
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
   :skolemid skolem_prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (<= 0 y)
    )
    (<= 0 (Mul x y))
   )
   :pattern ((Mul x y))
   :qid prelude_mul_nats
   :skolemid skolem_prelude_mul_nats
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucDiv x y))
     (<= (EucDiv x y) x)
   ))
   :pattern ((EucDiv x y))
   :qid prelude_div_unsigned_in_bounds
   :skolemid skolem_prelude_div_unsigned_in_bounds
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucMod x y))
     (< (EucMod x y) y)
   ))
   :pattern ((EucMod x y))
   :qid prelude_mod_unsigned_in_bounds
   :skolemid skolem_prelude_mod_unsigned_in_bounds
)))
(declare-fun bitxor (Poly Poly) Int)
(declare-fun bitand (Poly Poly) Int)
(declare-fun bitor (Poly Poly) Int)
(declare-fun bitshr (Poly Poly) Int)
(declare-fun bitshl (Poly Poly) Int)
(declare-fun bitnot (Poly) Int)
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitxor x y))
   )
   :pattern ((uClip bits (bitxor x y)))
   :qid prelude_bit_xor_u_inv
   :skolemid skolem_prelude_bit_xor_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitxor x y))
   )
   :pattern ((iClip bits (bitxor x y)))
   :qid prelude_bit_xor_i_inv
   :skolemid skolem_prelude_bit_xor_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitor x y))
   )
   :pattern ((uClip bits (bitor x y)))
   :qid prelude_bit_or_u_inv
   :skolemid skolem_prelude_bit_or_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitor x y))
   )
   :pattern ((iClip bits (bitor x y)))
   :qid prelude_bit_or_i_inv
   :skolemid skolem_prelude_bit_or_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitand x y))
   )
   :pattern ((uClip bits (bitand x y)))
   :qid prelude_bit_and_u_inv
   :skolemid skolem_prelude_bit_and_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitand x y))
   )
   :pattern ((iClip bits (bitand x y)))
   :qid prelude_bit_and_i_inv
   :skolemid skolem_prelude_bit_and_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (<= 0 (%I y))
    )
    (uInv bits (bitshr x y))
   )
   :pattern ((uClip bits (bitshr x y)))
   :qid prelude_bit_shr_u_inv
   :skolemid skolem_prelude_bit_shr_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (<= 0 (%I y))
    )
    (iInv bits (bitshr x y))
   )
   :pattern ((iClip bits (bitshr x y)))
   :qid prelude_bit_shr_i_inv
   :skolemid skolem_prelude_bit_shr_i_inv
)))
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
   :skolemid skolem_prelude_singularmod
)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun default_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))


;; MODULE 'root module'

;; Fuel
(declare-const fuel%vstd!set.axiom_set_new. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal_deep. FuelId)
(declare-const fuel%set_advanced!is_member. FuelId)
(declare-const fuel%set_advanced!set_union. FuelId)
(declare-const fuel%set_advanced!set_intersection. FuelId)
(declare-const fuel%set_advanced!set_difference. FuelId)
(declare-const fuel%set_advanced!is_subset. FuelId)
(declare-const fuel%set_advanced!power_set. FuelId)
(declare-const fuel%set_advanced!is_partition. FuelId)
(declare-const fuel%set_advanced!is_multiset. FuelId)
(declare-const fuel%set_advanced!multiset_contains. FuelId)
(declare-const fuel%set_advanced!multiset_multiplicity. FuelId)
(declare-const fuel%set_advanced!is_set_family. FuelId)
(declare-const fuel%set_advanced!family_union. FuelId)
(declare-const fuel%set_advanced!family_intersection. FuelId)
(declare-const fuel%set_advanced!set_comprehension. FuelId)
(declare-const fuel%set_advanced!filtered_set. FuelId)
(declare-const fuel%set_advanced!mapped_set. FuelId)
(declare-const fuel%set_advanced!graph_edges. FuelId)
(declare-const fuel%set_advanced!neighbors. FuelId)
(declare-const fuel%set_advanced!is_undirected. FuelId)
(declare-const fuel%set_advanced!has_path. FuelId)
(declare-const fuel%set_advanced!employee_table. FuelId)
(declare-const fuel%set_advanced!employee_names. FuelId)
(declare-const fuel%set_advanced!engineers. FuelId)
(declare-const fuel%set_advanced!engineering_employees. FuelId)
(declare-const fuel%set_advanced!pair_set. FuelId)
(declare-const fuel%set_advanced!are_disjoint. FuelId)
(declare-const fuel%set_advanced!are_overlapping. FuelId)
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
 (distinct fuel%vstd!set.axiom_set_new. fuel%vstd!set.axiom_set_ext_equal. fuel%vstd!set.axiom_set_ext_equal_deep.
  fuel%set_advanced!is_member. fuel%set_advanced!set_union. fuel%set_advanced!set_intersection.
  fuel%set_advanced!set_difference. fuel%set_advanced!is_subset. fuel%set_advanced!power_set.
  fuel%set_advanced!is_partition. fuel%set_advanced!is_multiset. fuel%set_advanced!multiset_contains.
  fuel%set_advanced!multiset_multiplicity. fuel%set_advanced!is_set_family. fuel%set_advanced!family_union.
  fuel%set_advanced!family_intersection. fuel%set_advanced!set_comprehension. fuel%set_advanced!filtered_set.
  fuel%set_advanced!mapped_set. fuel%set_advanced!graph_edges. fuel%set_advanced!neighbors.
  fuel%set_advanced!is_undirected. fuel%set_advanced!has_path. fuel%set_advanced!employee_table.
  fuel%set_advanced!employee_names. fuel%set_advanced!engineers. fuel%set_advanced!engineering_employees.
  fuel%set_advanced!pair_set. fuel%set_advanced!are_disjoint. fuel%set_advanced!are_overlapping.
  fuel%vstd!array.group_array_axioms. fuel%vstd!function.group_function_axioms. fuel%vstd!layout.group_layout_axioms.
  fuel%vstd!map.group_map_axioms. fuel%vstd!multiset.group_multiset_axioms. fuel%vstd!raw_ptr.group_raw_ptr_axioms.
  fuel%vstd!seq.group_seq_axioms. fuel%vstd!seq_lib.group_filter_ensures. fuel%vstd!seq_lib.group_seq_lib_default.
  fuel%vstd!set.group_set_axioms. fuel%vstd!set_lib.group_set_lib_default. fuel%vstd!slice.group_slice_axioms.
  fuel%vstd!string.group_string_axioms. fuel%vstd!std_specs.bits.group_bits_axioms.
  fuel%vstd!std_specs.control_flow.group_control_flow_axioms. fuel%vstd!std_specs.hash.group_hash_axioms.
  fuel%vstd!std_specs.range.group_range_axioms. fuel%vstd!std_specs.slice.group_slice_axioms.
  fuel%vstd!std_specs.vec.group_vec_axioms. fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.
  fuel%vstd!group_vstd_default.
))
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
(declare-sort vstd!set.Set<set_advanced!Name.>. 0)
(declare-sort vstd!set.Set<set_advanced!Node.>. 0)
(declare-sort vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
 0
)
(declare-sort vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>. 0)
(declare-datatypes ((set_advanced!Node. 0) (set_advanced!Name. 0) (set_advanced!Department.
   0
  ) (tuple%0. 0) (tuple%2. 0)
 ) (((set_advanced!Node./A) (set_advanced!Node./B) (set_advanced!Node./C) (set_advanced!Node./D))
  ((set_advanced!Name./Alice) (set_advanced!Name./Bob) (set_advanced!Name./Carol) (set_advanced!Name./David))
  ((set_advanced!Department./Engineering) (set_advanced!Department./Sales) (set_advanced!Department./Marketing))
  ((tuple%0./tuple%0)) ((tuple%2./tuple%2 (tuple%2./tuple%2/?0 Poly) (tuple%2./tuple%2/?1
     Poly
)))))
(declare-fun tuple%2./tuple%2/0 (tuple%2.) Poly)
(declare-fun tuple%2./tuple%2/1 (tuple%2.) Poly)
(declare-fun TYPE%fun%1. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-const TYPE%set_advanced!Node. Type)
(declare-const TYPE%set_advanced!Name. Type)
(declare-const TYPE%set_advanced!Department. Type)
(declare-fun TYPE%tuple%2. (Dcr Type Dcr Type) Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%vstd!set.Set<set_advanced!Name.>. (vstd!set.Set<set_advanced!Name.>.)
 Poly
)
(declare-fun %Poly%vstd!set.Set<set_advanced!Name.>. (Poly) vstd!set.Set<set_advanced!Name.>.)
(declare-fun Poly%vstd!set.Set<set_advanced!Node.>. (vstd!set.Set<set_advanced!Node.>.)
 Poly
)
(declare-fun %Poly%vstd!set.Set<set_advanced!Node.>. (Poly) vstd!set.Set<set_advanced!Node.>.)
(declare-fun Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
 (vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.) Poly
)
(declare-fun %Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
 (Poly) vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
)
(declare-fun Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>. (
  vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.
 ) Poly
)
(declare-fun %Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.
 (Poly) vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.
)
(declare-fun Poly%set_advanced!Node. (set_advanced!Node.) Poly)
(declare-fun %Poly%set_advanced!Node. (Poly) set_advanced!Node.)
(declare-fun Poly%set_advanced!Name. (set_advanced!Name.) Poly)
(declare-fun %Poly%set_advanced!Name. (Poly) set_advanced!Name.)
(declare-fun Poly%set_advanced!Department. (set_advanced!Department.) Poly)
(declare-fun %Poly%set_advanced!Department. (Poly) set_advanced!Department.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(declare-fun Poly%tuple%2. (tuple%2.) Poly)
(declare-fun %Poly%tuple%2. (Poly) tuple%2.)
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%fun%1. (Poly%fun%1. x)))
   :pattern ((Poly%fun%1. x))
   :qid internal_crate__fun__1_box_axiom_definition
   :skolemid skolem_internal_crate__fun__1_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%fun%1. (%Poly%fun%1. x)))
   )
   :pattern ((has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_unbox_axiom_definition
   :skolemid skolem_internal_crate__fun__1_unbox_axiom_definition
)))
(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x %%Function%%)) (!
   (=>
    (forall ((T%0 Poly)) (!
      (=>
       (has_type T%0 T%0&)
       (has_type (%%apply%%0 x T%0) T%1&)
      )
      :pattern ((has_type (%%apply%%0 x T%0) T%1&))
      :qid internal_crate__fun__1_constructor_inner_definition
      :skolemid skolem_internal_crate__fun__1_constructor_inner_definition
    ))
    (has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
   )
   :pattern ((has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_constructor_definition
   :skolemid skolem_internal_crate__fun__1_constructor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (has_type (%%apply%%0 x T%0) T%1&)
   )
   :pattern ((%%apply%%0 x T%0) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&.
      T%1&
   )))
   :qid internal_crate__fun__1_apply_definition
   :skolemid skolem_internal_crate__fun__1_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (height_lt (height (%%apply%%0 x T%0)) (height (fun_from_recursive_field (Poly%fun%1.
        (mk_fun x)
   )))))
   :pattern ((height (%%apply%%0 x T%0)) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_crate__fun__1_height_apply_definition
   :skolemid skolem_internal_crate__fun__1_height_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (forall ((T%0 Poly)) (!
       (=>
        (has_type T%0 T%0&)
        (ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1. y) T%0))
       )
       :pattern ((ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1.
           y
          ) T%0
       )))
       :qid internal_crate__fun__1_inner_ext_equal_definition
       :skolemid skolem_internal_crate__fun__1_inner_ext_equal_definition
    )))
    (ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_crate__fun__1_ext_equal_definition
   :skolemid skolem_internal_crate__fun__1_ext_equal_definition
)))
(assert
 (forall ((x vstd!set.Set<set_advanced!Name.>.)) (!
   (= x (%Poly%vstd!set.Set<set_advanced!Name.>. (Poly%vstd!set.Set<set_advanced!Name.>.
      x
   )))
   :pattern ((Poly%vstd!set.Set<set_advanced!Name.>. x))
   :qid internal_vstd__set__Set<set_advanced!Name.>_box_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<set_advanced!Name.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. $ TYPE%set_advanced!Name.))
    (= x (Poly%vstd!set.Set<set_advanced!Name.>. (%Poly%vstd!set.Set<set_advanced!Name.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!set.Set. $ TYPE%set_advanced!Name.)))
   :qid internal_vstd__set__Set<set_advanced!Name.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<set_advanced!Name.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<set_advanced!Name.>.)) (!
   (has_type (Poly%vstd!set.Set<set_advanced!Name.>. x) (TYPE%vstd!set.Set. $ TYPE%set_advanced!Name.))
   :pattern ((has_type (Poly%vstd!set.Set<set_advanced!Name.>. x) (TYPE%vstd!set.Set. $
      TYPE%set_advanced!Name.
   )))
   :qid internal_vstd__set__Set<set_advanced!Name.>_has_type_always_definition
   :skolemid skolem_internal_vstd__set__Set<set_advanced!Name.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!set.Set<set_advanced!Node.>.)) (!
   (= x (%Poly%vstd!set.Set<set_advanced!Node.>. (Poly%vstd!set.Set<set_advanced!Node.>.
      x
   )))
   :pattern ((Poly%vstd!set.Set<set_advanced!Node.>. x))
   :qid internal_vstd__set__Set<set_advanced!Node.>_box_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<set_advanced!Node.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. $ TYPE%set_advanced!Node.))
    (= x (Poly%vstd!set.Set<set_advanced!Node.>. (%Poly%vstd!set.Set<set_advanced!Node.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!set.Set. $ TYPE%set_advanced!Node.)))
   :qid internal_vstd__set__Set<set_advanced!Node.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<set_advanced!Node.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<set_advanced!Node.>.)) (!
   (has_type (Poly%vstd!set.Set<set_advanced!Node.>. x) (TYPE%vstd!set.Set. $ TYPE%set_advanced!Node.))
   :pattern ((has_type (Poly%vstd!set.Set<set_advanced!Node.>. x) (TYPE%vstd!set.Set. $
      TYPE%set_advanced!Node.
   )))
   :qid internal_vstd__set__Set<set_advanced!Node.>_has_type_always_definition
   :skolemid skolem_internal_vstd__set__Set<set_advanced!Node.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.))
  (!
   (= x (%Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>. (Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
      x
   )))
   :pattern ((Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
     x
   ))
   :qid internal_vstd__set__Set<tuple__2<set_advanced!Name./set_advanced!Department.>.>_box_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<tuple__2<set_advanced!Name./set_advanced!Department.>.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $ TYPE%set_advanced!Department.)))
    (= x (Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>. (%Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name.
       $ TYPE%set_advanced!Department.
   ))))
   :qid internal_vstd__set__Set<tuple__2<set_advanced!Name./set_advanced!Department.>.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<tuple__2<set_advanced!Name./set_advanced!Department.>.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.))
  (!
   (has_type (Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
     x
    ) (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $ TYPE%set_advanced!Department.))
   )
   :pattern ((has_type (Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
      x
     ) (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $ TYPE%set_advanced!Department.))
   ))
   :qid internal_vstd__set__Set<tuple__2<set_advanced!Name./set_advanced!Department.>.>_has_type_always_definition
   :skolemid skolem_internal_vstd__set__Set<tuple__2<set_advanced!Name./set_advanced!Department.>.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.)) (!
   (= x (%Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>. (Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.
      x
   )))
   :pattern ((Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>. x))
   :qid internal_vstd__set__Set<tuple__2<set_advanced!Node./set_advanced!Node.>.>_box_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<tuple__2<set_advanced!Node./set_advanced!Node.>.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.)))
    (= x (Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>. (%Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node.
       $ TYPE%set_advanced!Node.
   ))))
   :qid internal_vstd__set__Set<tuple__2<set_advanced!Node./set_advanced!Node.>.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<tuple__2<set_advanced!Node./set_advanced!Node.>.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.)) (!
   (has_type (Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>. x)
    (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.))
   )
   :pattern ((has_type (Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.
      x
     ) (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.))
   ))
   :qid internal_vstd__set__Set<tuple__2<set_advanced!Node./set_advanced!Node.>.>_has_type_always_definition
   :skolemid skolem_internal_vstd__set__Set<tuple__2<set_advanced!Node./set_advanced!Node.>.>_has_type_always_definition
)))
(assert
 (forall ((x set_advanced!Node.)) (!
   (= x (%Poly%set_advanced!Node. (Poly%set_advanced!Node. x)))
   :pattern ((Poly%set_advanced!Node. x))
   :qid internal_set_advanced__Node_box_axiom_definition
   :skolemid skolem_internal_set_advanced__Node_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%set_advanced!Node.)
    (= x (Poly%set_advanced!Node. (%Poly%set_advanced!Node. x)))
   )
   :pattern ((has_type x TYPE%set_advanced!Node.))
   :qid internal_set_advanced__Node_unbox_axiom_definition
   :skolemid skolem_internal_set_advanced__Node_unbox_axiom_definition
)))
(assert
 (forall ((x set_advanced!Node.)) (!
   (has_type (Poly%set_advanced!Node. x) TYPE%set_advanced!Node.)
   :pattern ((has_type (Poly%set_advanced!Node. x) TYPE%set_advanced!Node.))
   :qid internal_set_advanced__Node_has_type_always_definition
   :skolemid skolem_internal_set_advanced__Node_has_type_always_definition
)))
(assert
 (forall ((x set_advanced!Name.)) (!
   (= x (%Poly%set_advanced!Name. (Poly%set_advanced!Name. x)))
   :pattern ((Poly%set_advanced!Name. x))
   :qid internal_set_advanced__Name_box_axiom_definition
   :skolemid skolem_internal_set_advanced__Name_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%set_advanced!Name.)
    (= x (Poly%set_advanced!Name. (%Poly%set_advanced!Name. x)))
   )
   :pattern ((has_type x TYPE%set_advanced!Name.))
   :qid internal_set_advanced__Name_unbox_axiom_definition
   :skolemid skolem_internal_set_advanced__Name_unbox_axiom_definition
)))
(assert
 (forall ((x set_advanced!Name.)) (!
   (has_type (Poly%set_advanced!Name. x) TYPE%set_advanced!Name.)
   :pattern ((has_type (Poly%set_advanced!Name. x) TYPE%set_advanced!Name.))
   :qid internal_set_advanced__Name_has_type_always_definition
   :skolemid skolem_internal_set_advanced__Name_has_type_always_definition
)))
(assert
 (forall ((x set_advanced!Department.)) (!
   (= x (%Poly%set_advanced!Department. (Poly%set_advanced!Department. x)))
   :pattern ((Poly%set_advanced!Department. x))
   :qid internal_set_advanced__Department_box_axiom_definition
   :skolemid skolem_internal_set_advanced__Department_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%set_advanced!Department.)
    (= x (Poly%set_advanced!Department. (%Poly%set_advanced!Department. x)))
   )
   :pattern ((has_type x TYPE%set_advanced!Department.))
   :qid internal_set_advanced__Department_unbox_axiom_definition
   :skolemid skolem_internal_set_advanced__Department_unbox_axiom_definition
)))
(assert
 (forall ((x set_advanced!Department.)) (!
   (has_type (Poly%set_advanced!Department. x) TYPE%set_advanced!Department.)
   :pattern ((has_type (Poly%set_advanced!Department. x) TYPE%set_advanced!Department.))
   :qid internal_set_advanced__Department_has_type_always_definition
   :skolemid skolem_internal_set_advanced__Department_has_type_always_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (= x (%Poly%tuple%0. (Poly%tuple%0. x)))
   :pattern ((Poly%tuple%0. x))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%tuple%0.)
    (= x (Poly%tuple%0. (%Poly%tuple%0. x)))
   )
   :pattern ((has_type x TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (has_type (Poly%tuple%0. x) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= x (%Poly%tuple%2. (Poly%tuple%2. x)))
   :pattern ((Poly%tuple%2. x))
   :qid internal_crate__tuple__2_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__2_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%tuple%2. (%Poly%tuple%2. x)))
   )
   :pattern ((has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__tuple__2_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__2_unbox_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (_0! Poly) (_1! Poly)) (!
   (=>
    (and
     (has_type _0! T%0&)
     (has_type _1! T%1&)
    )
    (has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&. T%0& T%1&.
      T%1&
   )))
   :pattern ((has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&.
      T%0& T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2_constructor_definition
   :skolemid skolem_internal_tuple__2./tuple__2_constructor_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/0 x) (tuple%2./tuple%2/?0 x))
   :pattern ((tuple%2./tuple%2/0 x))
   :qid internal_tuple__2./tuple__2/0_accessor_definition
   :skolemid skolem_internal_tuple__2./tuple__2/0_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) T%0&)
   )
   :pattern ((tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/0_invariant_definition
   :skolemid skolem_internal_tuple__2./tuple__2/0_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/1 x) (tuple%2./tuple%2/?1 x))
   :pattern ((tuple%2./tuple%2/1 x))
   :qid internal_tuple__2./tuple__2/1_accessor_definition
   :skolemid skolem_internal_tuple__2./tuple__2/1_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) T%1&)
   )
   :pattern ((tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/1_invariant_definition
   :skolemid skolem_internal_tuple__2./tuple__2/1_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    ((_ is tuple%2./tuple%2) x)
    (height_lt (height (tuple%2./tuple%2/0 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/0 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/0
   :skolemid skolem_prelude_datatype_height_tuple%2./tuple%2/0
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    ((_ is tuple%2./tuple%2) x)
    (height_lt (height (tuple%2./tuple%2/1 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/1 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/1
   :skolemid skolem_prelude_datatype_height_tuple%2./tuple%2/1
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (ext_eq deep T%0& (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (tuple%2./tuple%2/0 (%Poly%tuple%2.
        y
     )))
     (ext_eq deep T%1& (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (tuple%2./tuple%2/1 (%Poly%tuple%2.
        y
    ))))
    (ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_tuple__2./tuple__2_ext_equal_definition
   :skolemid skolem_internal_tuple__2./tuple__2_ext_equal_definition
)))

;; Function-Decl vstd::set::Set::contains
(declare-fun vstd!set.Set.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::set::impl&%0::new
(declare-fun vstd!set.impl&%0.new.? (Dcr Type Poly) Poly)

;; Function-Decl set_advanced::is_member
(declare-fun set_advanced!is_member.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_advanced::set_union
(declare-fun set_advanced!set_union.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_advanced::set_intersection
(declare-fun set_advanced!set_intersection.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_advanced::set_difference
(declare-fun set_advanced!set_difference.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_advanced::is_subset
(declare-fun set_advanced!is_subset.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_advanced::power_set
(declare-fun set_advanced!power_set.? (Dcr Type Poly) Poly)

;; Function-Decl set_advanced::is_partition
(declare-fun set_advanced!is_partition.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_advanced::is_multiset
(declare-fun set_advanced!is_multiset.? (Dcr Type Poly) Bool)

;; Function-Decl set_advanced::multiset_contains
(declare-fun set_advanced!multiset_contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_advanced::multiset_multiplicity
(declare-fun set_advanced!multiset_multiplicity.? (Dcr Type Poly Poly) Int)

;; Function-Decl set_advanced::is_set_family
(declare-fun set_advanced!is_set_family.? (Dcr Type Poly) Bool)

;; Function-Decl set_advanced::family_union
(declare-fun set_advanced!family_union.? (Dcr Type Poly) Poly)

;; Function-Decl set_advanced::family_intersection
(declare-fun set_advanced!family_intersection.? (Dcr Type Poly) Poly)

;; Function-Decl set_advanced::set_comprehension
(declare-fun set_advanced!set_comprehension.? (Dcr Type Poly) Poly)

;; Function-Decl set_advanced::filtered_set
(declare-fun set_advanced!filtered_set.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_advanced::mapped_set
(declare-fun set_advanced!mapped_set.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl set_advanced::graph_edges
(declare-fun set_advanced!graph_edges.? (Poly) vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.)

;; Function-Decl set_advanced::neighbors
(declare-fun set_advanced!neighbors.? (Poly Poly) vstd!set.Set<set_advanced!Node.>.)

;; Function-Decl set_advanced::is_undirected
(declare-fun set_advanced!is_undirected.? (Poly) Bool)

;; Function-Decl set_advanced::has_path
(declare-fun set_advanced!has_path.? (Poly Poly Poly Poly) Bool)

;; Function-Decl set_advanced::employee_table
(declare-fun set_advanced!employee_table.? (Poly) vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.)

;; Function-Decl set_advanced::employee_names
(declare-fun set_advanced!employee_names.? (Poly) vstd!set.Set<set_advanced!Name.>.)

;; Function-Decl set_advanced::engineers
(declare-fun set_advanced!engineers.? (Poly) vstd!set.Set<set_advanced!Name.>.)

;; Function-Decl set_advanced::engineering_employees
(declare-fun set_advanced!engineering_employees.? (Poly) vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.)

;; Function-Decl set_advanced::pair_set
(declare-fun set_advanced!pair_set.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_advanced::are_disjoint
(declare-fun set_advanced!are_disjoint.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_advanced::are_overlapping
(declare-fun set_advanced!are_overlapping.? (Dcr Type Poly Poly) Bool)

;; Function-Axioms vstd::set::impl&%0::new
(assert
 (forall ((A&. Dcr) (A& Type) (f! Poly)) (!
   (=>
    (has_type f! (TYPE%fun%1. A&. A& $ BOOL))
    (has_type (vstd!set.impl&%0.new.? A&. A& f!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.new.? A&. A& f!))
   :qid internal_vstd!set.impl&__0.new.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.impl&__0.new.?_pre_post_definition
)))

;; Broadcast vstd::set::axiom_set_new
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
    :qid user_vstd__set__axiom_set_new_0
    :skolemid skolem_user_vstd__set__axiom_set_new_0
))))

;; Broadcast vstd::set::axiom_set_ext_equal
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
         :qid user_vstd__set__axiom_set_ext_equal_1
         :skolemid skolem_user_vstd__set__axiom_set_ext_equal_1
    )))))
    :pattern ((ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!))
    :qid user_vstd__set__axiom_set_ext_equal_2
    :skolemid skolem_user_vstd__set__axiom_set_ext_equal_2
))))

;; Broadcast vstd::set::axiom_set_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_ext_equal_deep.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!) (ext_eq false (TYPE%vstd!set.Set.
         A&. A&
        ) s1! s2!
    ))))
    :pattern ((ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!))
    :qid user_vstd__set__axiom_set_ext_equal_deep_3
    :skolemid skolem_user_vstd__set__axiom_set_ext_equal_deep_3
))))

;; Function-Axioms set_advanced::is_member
(assert
 (fuel_bool_default fuel%set_advanced!is_member.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!is_member.)
  (forall ((T&. Dcr) (T& Type) (x! Poly) (set! Poly)) (!
    (= (set_advanced!is_member.? T&. T& x! set!) (vstd!set.Set.contains.? T&. T& set! x!))
    :pattern ((set_advanced!is_member.? T&. T& x! set!))
    :qid internal_set_advanced!is_member.?_definition
    :skolemid skolem_internal_set_advanced!is_member.?_definition
))))

;; Function-Axioms set_advanced::set_union
(assert
 (fuel_bool_default fuel%set_advanced!set_union.)
)
(declare-fun %%lambda%%0 (Dcr Type Poly Dcr Type Poly) %%Function%%)
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
(assert
 (=>
  (fuel_bool fuel%set_advanced!set_union.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_advanced!set_union.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%0 T&. T& s1! T&. T& s2!))
    )))
    :pattern ((set_advanced!set_union.? T&. T& s1! s2!))
    :qid internal_set_advanced!set_union.?_definition
    :skolemid skolem_internal_set_advanced!set_union.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_advanced!set_union.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_advanced!set_union.? T&. T& s1! s2!))
   :qid internal_set_advanced!set_union.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!set_union.?_pre_post_definition
)))

;; Function-Axioms set_advanced::set_intersection
(assert
 (fuel_bool_default fuel%set_advanced!set_intersection.)
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
  (fuel_bool fuel%set_advanced!set_intersection.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_advanced!set_intersection.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T&
      (Poly%fun%1. (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!)))
    ))
    :pattern ((set_advanced!set_intersection.? T&. T& s1! s2!))
    :qid internal_set_advanced!set_intersection.?_definition
    :skolemid skolem_internal_set_advanced!set_intersection.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_advanced!set_intersection.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&.
      T&
   )))
   :pattern ((set_advanced!set_intersection.? T&. T& s1! s2!))
   :qid internal_set_advanced!set_intersection.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!set_intersection.?_pre_post_definition
)))

;; Function-Axioms set_advanced::set_difference
(assert
 (fuel_bool_default fuel%set_advanced!set_difference.)
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
  (fuel_bool fuel%set_advanced!set_difference.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_advanced!set_difference.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%2 T&. T& s1! T&. T& s2!))
    )))
    :pattern ((set_advanced!set_difference.? T&. T& s1! s2!))
    :qid internal_set_advanced!set_difference.?_definition
    :skolemid skolem_internal_set_advanced!set_difference.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_advanced!set_difference.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_advanced!set_difference.? T&. T& s1! s2!))
   :qid internal_set_advanced!set_difference.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!set_difference.?_pre_post_definition
)))

;; Function-Axioms set_advanced::is_subset
(assert
 (fuel_bool_default fuel%set_advanced!is_subset.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!is_subset.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_advanced!is_subset.? T&. T& s1! s2!) (forall ((x$ Poly)) (!
       (=>
        (has_type x$ T&)
        (=>
         (vstd!set.Set.contains.? T&. T& s1! x$)
         (vstd!set.Set.contains.? T&. T& s2! x$)
       ))
       :pattern ((vstd!set.Set.contains.? T&. T& s1! x$))
       :pattern ((vstd!set.Set.contains.? T&. T& s2! x$))
       :qid user_set_advanced__is_subset_4
       :skolemid skolem_user_set_advanced__is_subset_4
    )))
    :pattern ((set_advanced!is_subset.? T&. T& s1! s2!))
    :qid internal_set_advanced!is_subset.?_definition
    :skolemid skolem_internal_set_advanced!is_subset.?_definition
))))

;; Function-Axioms set_advanced::power_set
(assert
 (fuel_bool_default fuel%set_advanced!power_set.)
)
(declare-fun %%lambda%%3 (Dcr Type Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (subset$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%3 %%hole%%0 %%hole%%1 %%hole%%2) subset$) (B (set_advanced!is_subset.?
      %%hole%%0 %%hole%%1 subset$ %%hole%%2
   )))
   :pattern ((%%apply%%0 (%%lambda%%3 %%hole%%0 %%hole%%1 %%hole%%2) subset$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!power_set.)
  (forall ((T&. Dcr) (T& Type) (s! Poly)) (!
    (= (set_advanced!power_set.? T&. T& s!) (vstd!set.impl&%0.new.? $ (TYPE%vstd!set.Set.
       T&. T&
      ) (Poly%fun%1. (mk_fun (%%lambda%%3 T&. T& s!)))
    ))
    :pattern ((set_advanced!power_set.? T&. T& s!))
    :qid internal_set_advanced!power_set.?_definition
    :skolemid skolem_internal_set_advanced!power_set.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s! Poly)) (!
   (=>
    (has_type s! (TYPE%vstd!set.Set. T&. T&))
    (has_type (set_advanced!power_set.? T&. T& s!) (TYPE%vstd!set.Set. $ (TYPE%vstd!set.Set.
       T&. T&
   ))))
   :pattern ((set_advanced!power_set.? T&. T& s!))
   :qid internal_set_advanced!power_set.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!power_set.?_pre_post_definition
)))

;; Function-Axioms set_advanced::is_partition
(assert
 (fuel_bool_default fuel%set_advanced!is_partition.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!is_partition.)
  (forall ((T&. Dcr) (T& Type) (partition! Poly) (original! Poly)) (!
    (= (set_advanced!is_partition.? T&. T& partition! original!) (forall ((subset$ Poly))
      (!
       (=>
        (has_type subset$ (TYPE%vstd!set.Set. T&. T&))
        (=>
         (vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! subset$)
         (exists ((x$ Poly)) (!
           (and
            (has_type x$ T&)
            (and
             (vstd!set.Set.contains.? T&. T& subset$ x$)
             (forall ((s1$ Poly) (s2$ Poly)) (!
               (=>
                (and
                 (has_type s1$ (TYPE%vstd!set.Set. T&. T&))
                 (has_type s2$ (TYPE%vstd!set.Set. T&. T&))
                )
                (and
                 (=>
                  (and
                   (and
                    (vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! s1$)
                    (vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! s2$)
                   )
                   (not (= s1$ s2$))
                  )
                  (forall ((x$0 Poly)) (!
                    (=>
                     (has_type x$0 T&)
                     (not (and
                       (vstd!set.Set.contains.? T&. T& s1$ x$0)
                       (vstd!set.Set.contains.? T&. T& s2$ x$0)
                    )))
                    :pattern ((vstd!set.Set.contains.? T&. T& s1$ x$0))
                    :pattern ((vstd!set.Set.contains.? T&. T& s2$ x$0))
                    :qid user_set_advanced__is_partition_5
                    :skolemid skolem_user_set_advanced__is_partition_5
                 )))
                 (forall ((x$1 Poly)) (!
                   (=>
                    (has_type x$1 T&)
                    (= (vstd!set.Set.contains.? T&. T& original! x$1) (exists ((subset$0 Poly)) (!
                       (and
                        (has_type subset$0 (TYPE%vstd!set.Set. T&. T&))
                        (and
                         (vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! subset$0)
                         (vstd!set.Set.contains.? T&. T& subset$0 x$1)
                       ))
                       :pattern ((vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! subset$0))
                       :pattern ((vstd!set.Set.contains.? T&. T& subset$0 x$1))
                       :qid user_set_advanced__is_partition_6
                       :skolemid skolem_user_set_advanced__is_partition_6
                   ))))
                   :pattern ((vstd!set.Set.contains.? T&. T& original! x$1))
                   :qid user_set_advanced__is_partition_7
                   :skolemid skolem_user_set_advanced__is_partition_7
               ))))
               :pattern ((vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! s1$) (
                 vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! s2$
               ))
               :qid user_set_advanced__is_partition_8
               :skolemid skolem_user_set_advanced__is_partition_8
           ))))
           :pattern ((vstd!set.Set.contains.? T&. T& subset$ x$))
           :qid user_set_advanced__is_partition_9
           :skolemid skolem_user_set_advanced__is_partition_9
       ))))
       :pattern ((vstd!set.Set.contains.? $ (TYPE%vstd!set.Set. T&. T&) partition! subset$))
       :qid user_set_advanced__is_partition_10
       :skolemid skolem_user_set_advanced__is_partition_10
    )))
    :pattern ((set_advanced!is_partition.? T&. T& partition! original!))
    :qid internal_set_advanced!is_partition.?_definition
    :skolemid skolem_internal_set_advanced!is_partition.?_definition
))))

;; Function-Axioms set_advanced::is_multiset
(assert
 (fuel_bool_default fuel%set_advanced!is_multiset.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!is_multiset.)
  (forall ((T&. Dcr) (T& Type) (bag! Poly)) (!
    (= (set_advanced!is_multiset.? T&. T& bag!) (forall ((x$ Poly) (n1$ Poly) (n2$ Poly))
      (!
       (=>
        (and
         (has_type x$ T&)
         (has_type n1$ NAT)
         (has_type n2$ NAT)
        )
        (=>
         (and
          (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2. (
             tuple%2./tuple%2 x$ n1$
          )))
          (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2. (
             tuple%2./tuple%2 x$ n2$
         ))))
         (= n1$ n2$)
       ))
       :pattern ((vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2.
          (tuple%2./tuple%2 x$ n1$)
         )
        ) (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2.
          (tuple%2./tuple%2 x$ n2$)
       )))
       :pattern ((vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2.
          (tuple%2./tuple%2 x$ n1$)
         )
        ) (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2.
          (tuple%2./tuple%2 x$ n2$)
       )))
       :qid user_set_advanced__is_multiset_11
       :skolemid skolem_user_set_advanced__is_multiset_11
    )))
    :pattern ((set_advanced!is_multiset.? T&. T& bag!))
    :qid internal_set_advanced!is_multiset.?_definition
    :skolemid skolem_internal_set_advanced!is_multiset.?_definition
))))

;; Function-Axioms set_advanced::multiset_contains
(assert
 (fuel_bool_default fuel%set_advanced!multiset_contains.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!multiset_contains.)
  (forall ((T&. Dcr) (T& Type) (x! Poly) (bag! Poly)) (!
    (= (set_advanced!multiset_contains.? T&. T& x! bag!) (exists ((n$ Poly)) (!
       (and
        (has_type n$ NAT)
        (and
         (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2. (
            tuple%2./tuple%2 x! n$
         )))
         (> (%I n$) 0)
       ))
       :pattern ((vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! (Poly%tuple%2.
          (tuple%2./tuple%2 x! n$)
       )))
       :qid user_set_advanced__multiset_contains_12
       :skolemid skolem_user_set_advanced__multiset_contains_12
    )))
    :pattern ((set_advanced!multiset_contains.? T&. T& x! bag!))
    :qid internal_set_advanced!multiset_contains.?_definition
    :skolemid skolem_internal_set_advanced!multiset_contains.?_definition
))))

;; Function-Axioms set_advanced::multiset_multiplicity
(assert
 (fuel_bool_default fuel%set_advanced!multiset_multiplicity.)
)
(declare-fun %%choose%%0 (Type Poly Dcr Type Poly Int Poly Dcr Type Poly) Poly)
(assert
 (forall ((%%hole%%0 Type) (%%hole%%1 Poly) (%%hole%%2 Dcr) (%%hole%%3 Type) (%%hole%%4
    Poly
   ) (%%hole%%5 Int) (%%hole%%6 Poly) (%%hole%%7 Dcr) (%%hole%%8 Type) (%%hole%%9 Poly)
  ) (!
   (=>
    (exists ((n$ Poly)) (!
      (and
       (has_type n$ %%hole%%0)
       (and
        (vstd!set.Set.contains.? %%hole%%2 %%hole%%3 %%hole%%4 (Poly%tuple%2. (tuple%2./tuple%2
           %%hole%%1 n$
        )))
        (> (%I n$) %%hole%%5)
      ))
      :pattern ((vstd!set.Set.contains.? %%hole%%7 %%hole%%8 %%hole%%9 (Poly%tuple%2. (tuple%2./tuple%2
          %%hole%%6 n$
      ))))
      :qid user_set_advanced__multiset_multiplicity_13
      :skolemid skolem_user_set_advanced__multiset_multiplicity_13
    ))
    (exists ((n$ Poly)) (!
      (and
       (and
        (has_type n$ %%hole%%0)
        (and
         (vstd!set.Set.contains.? %%hole%%2 %%hole%%3 %%hole%%4 (Poly%tuple%2. (tuple%2./tuple%2
            %%hole%%1 n$
         )))
         (> (%I n$) %%hole%%5)
       ))
       (= (%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5 %%hole%%6
         %%hole%%7 %%hole%%8 %%hole%%9
        ) n$
      ))
      :pattern ((vstd!set.Set.contains.? %%hole%%7 %%hole%%8 %%hole%%9 (Poly%tuple%2. (tuple%2./tuple%2
          %%hole%%6 n$
   )))))))
   :pattern ((%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
     %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9
)))))
(assert
 (=>
  (fuel_bool fuel%set_advanced!multiset_multiplicity.)
  (forall ((T&. Dcr) (T& Type) (x! Poly) (bag! Poly)) (!
    (= (set_advanced!multiset_multiplicity.? T&. T& x! bag!) (%I (as_type (%%choose%%0 NAT
        x! (DST $) (TYPE%tuple%2. T&. T& $ NAT) bag! 0 x! (DST $) (TYPE%tuple%2. T&. T& $
         NAT
        ) bag!
       ) NAT
    )))
    :pattern ((set_advanced!multiset_multiplicity.? T&. T& x! bag!))
    :qid internal_set_advanced!multiset_multiplicity.?_definition
    :skolemid skolem_internal_set_advanced!multiset_multiplicity.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly) (bag! Poly)) (!
   (=>
    (and
     (has_type x! T&)
     (has_type bag! (TYPE%vstd!set.Set. (DST $) (TYPE%tuple%2. T&. T& $ NAT)))
    )
    (<= 0 (set_advanced!multiset_multiplicity.? T&. T& x! bag!))
   )
   :pattern ((set_advanced!multiset_multiplicity.? T&. T& x! bag!))
   :qid internal_set_advanced!multiset_multiplicity.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!multiset_multiplicity.?_pre_post_definition
)))

;; Function-Axioms set_advanced::is_set_family
(assert
 (fuel_bool_default fuel%set_advanced!is_set_family.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!is_set_family.)
  (forall ((T&. Dcr) (T& Type) (family! Poly)) (!
    (= (set_advanced!is_set_family.? T&. T& family!) true)
    :pattern ((set_advanced!is_set_family.? T&. T& family!))
    :qid internal_set_advanced!is_set_family.?_definition
    :skolemid skolem_internal_set_advanced!is_set_family.?_definition
))))

;; Function-Axioms set_advanced::family_union
(assert
 (fuel_bool_default fuel%set_advanced!family_union.)
)
(declare-fun %%lambda%%4 (Dcr Type Poly Dcr Type Type Dcr Type Poly Dcr Type) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 Dcr) (%%hole%%4
    Type
   ) (%%hole%%5 Type) (%%hole%%6 Dcr) (%%hole%%7 Type) (%%hole%%8 Poly) (%%hole%%9 Dcr)
   (%%hole%%10 Type) (x$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%4 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
      %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9 %%hole%%10
     ) x$
    ) (B (exists ((s$ Poly)) (!
       (and
        (has_type s$ %%hole%%5)
        (and
         (vstd!set.Set.contains.? %%hole%%6 %%hole%%7 %%hole%%8 s$)
         (vstd!set.Set.contains.? %%hole%%9 %%hole%%10 s$ x$)
       ))
       :pattern ((vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 s$))
       :pattern ((vstd!set.Set.contains.? %%hole%%3 %%hole%%4 s$ x$))
       :qid user_set_advanced__family_union_14
       :skolemid skolem_user_set_advanced__family_union_14
   ))))
   :pattern ((%%apply%%0 (%%lambda%%4 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5 %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9 %%hole%%10
     ) x$
)))))
(assert
 (=>
  (fuel_bool fuel%set_advanced!family_union.)
  (forall ((T&. Dcr) (T& Type) (family! Poly)) (!
    (= (set_advanced!family_union.? T&. T& family!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%4 $ (TYPE%vstd!set.Set. T&. T&) family! T&. T& (TYPE%vstd!set.Set.
          T&. T&
         ) $ (TYPE%vstd!set.Set. T&. T&) family! T&. T&
    )))))
    :pattern ((set_advanced!family_union.? T&. T& family!))
    :qid internal_set_advanced!family_union.?_definition
    :skolemid skolem_internal_set_advanced!family_union.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (family! Poly)) (!
   (=>
    (has_type family! (TYPE%vstd!set.Set. $ (TYPE%vstd!set.Set. T&. T&)))
    (has_type (set_advanced!family_union.? T&. T& family!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_advanced!family_union.? T&. T& family!))
   :qid internal_set_advanced!family_union.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!family_union.?_pre_post_definition
)))

;; Function-Axioms set_advanced::family_intersection
(assert
 (fuel_bool_default fuel%set_advanced!family_intersection.)
)
(declare-fun %%lambda%%5 (Dcr Type Poly Dcr Type Type Dcr Type Poly Dcr Type) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 Dcr) (%%hole%%4
    Type
   ) (%%hole%%5 Type) (%%hole%%6 Dcr) (%%hole%%7 Type) (%%hole%%8 Poly) (%%hole%%9 Dcr)
   (%%hole%%10 Type) (x$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%5 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
      %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9 %%hole%%10
     ) x$
    ) (B (forall ((s$ Poly)) (!
       (=>
        (has_type s$ %%hole%%5)
        (=>
         (vstd!set.Set.contains.? %%hole%%6 %%hole%%7 %%hole%%8 s$)
         (vstd!set.Set.contains.? %%hole%%9 %%hole%%10 s$ x$)
       ))
       :pattern ((vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 s$))
       :pattern ((vstd!set.Set.contains.? %%hole%%3 %%hole%%4 s$ x$))
       :qid user_set_advanced__family_intersection_15
       :skolemid skolem_user_set_advanced__family_intersection_15
   ))))
   :pattern ((%%apply%%0 (%%lambda%%5 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5 %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9 %%hole%%10
     ) x$
)))))
(assert
 (=>
  (fuel_bool fuel%set_advanced!family_intersection.)
  (forall ((T&. Dcr) (T& Type) (family! Poly)) (!
    (= (set_advanced!family_intersection.? T&. T& family!) (vstd!set.impl&%0.new.? T&.
      T& (Poly%fun%1. (mk_fun (%%lambda%%5 $ (TYPE%vstd!set.Set. T&. T&) family! T&. T& (TYPE%vstd!set.Set.
          T&. T&
         ) $ (TYPE%vstd!set.Set. T&. T&) family! T&. T&
    )))))
    :pattern ((set_advanced!family_intersection.? T&. T& family!))
    :qid internal_set_advanced!family_intersection.?_definition
    :skolemid skolem_internal_set_advanced!family_intersection.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (family! Poly)) (!
   (=>
    (has_type family! (TYPE%vstd!set.Set. $ (TYPE%vstd!set.Set. T&. T&)))
    (has_type (set_advanced!family_intersection.? T&. T& family!) (TYPE%vstd!set.Set. T&.
      T&
   )))
   :pattern ((set_advanced!family_intersection.? T&. T& family!))
   :qid internal_set_advanced!family_intersection.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!family_intersection.?_pre_post_definition
)))

;; Function-Axioms set_advanced::set_comprehension
(assert
 (fuel_bool_default fuel%set_advanced!set_comprehension.)
)
(declare-fun %%lambda%%6 (%%Function%%) %%Function%%)
(assert
 (forall ((%%hole%%0 %%Function%%) (x$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%6 %%hole%%0) x$) (%%apply%%0 %%hole%%0 x$))
   :pattern ((%%apply%%0 (%%lambda%%6 %%hole%%0) x$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!set_comprehension.)
  (forall ((T&. Dcr) (T& Type) (predicate! Poly)) (!
    (= (set_advanced!set_comprehension.? T&. T& predicate!) (vstd!set.impl&%0.new.? T&.
      T& (Poly%fun%1. (mk_fun (%%lambda%%6 (%Poly%fun%1. predicate!))))
    ))
    :pattern ((set_advanced!set_comprehension.? T&. T& predicate!))
    :qid internal_set_advanced!set_comprehension.?_definition
    :skolemid skolem_internal_set_advanced!set_comprehension.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (predicate! Poly)) (!
   (=>
    (has_type predicate! (TYPE%fun%1. T&. T& $ BOOL))
    (has_type (set_advanced!set_comprehension.? T&. T& predicate!) (TYPE%vstd!set.Set.
      T&. T&
   )))
   :pattern ((set_advanced!set_comprehension.? T&. T& predicate!))
   :qid internal_set_advanced!set_comprehension.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!set_comprehension.?_pre_post_definition
)))

;; Function-Axioms set_advanced::filtered_set
(assert
 (fuel_bool_default fuel%set_advanced!filtered_set.)
)
(declare-fun %%lambda%%7 (Dcr Type Poly %%Function%%) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 %%Function%%)
   (x$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%7 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) x$) (B (and
      (vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 x$)
      (%B (%%apply%%0 %%hole%%3 x$))
   )))
   :pattern ((%%apply%%0 (%%lambda%%7 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) x$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!filtered_set.)
  (forall ((T&. Dcr) (T& Type) (s! Poly) (predicate! Poly)) (!
    (= (set_advanced!filtered_set.? T&. T& s! predicate!) (vstd!set.impl&%0.new.? T&. T&
      (Poly%fun%1. (mk_fun (%%lambda%%7 T&. T& s! (%Poly%fun%1. predicate!))))
    ))
    :pattern ((set_advanced!filtered_set.? T&. T& s! predicate!))
    :qid internal_set_advanced!filtered_set.?_definition
    :skolemid skolem_internal_set_advanced!filtered_set.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s! Poly) (predicate! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. T&. T&))
     (has_type predicate! (TYPE%fun%1. T&. T& $ BOOL))
    )
    (has_type (set_advanced!filtered_set.? T&. T& s! predicate!) (TYPE%vstd!set.Set. T&.
      T&
   )))
   :pattern ((set_advanced!filtered_set.? T&. T& s! predicate!))
   :qid internal_set_advanced!filtered_set.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!filtered_set.?_pre_post_definition
)))

;; Function-Axioms set_advanced::mapped_set
(assert
 (fuel_bool_default fuel%set_advanced!mapped_set.)
)
(declare-fun %%lambda%%8 (Dcr Type Poly Type Dcr Type Poly %%Function%%) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 Type) (%%hole%%4
    Dcr
   ) (%%hole%%5 Type) (%%hole%%6 Poly) (%%hole%%7 %%Function%%) (y$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%8 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
      %%hole%%6 %%hole%%7
     ) y$
    ) (B (exists ((x$ Poly)) (!
       (and
        (has_type x$ %%hole%%3)
        (and
         (vstd!set.Set.contains.? %%hole%%4 %%hole%%5 %%hole%%6 x$)
         (= y$ (%%apply%%0 %%hole%%7 x$))
       ))
       :pattern ((vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 x$))
       :qid user_set_advanced__mapped_set_16
       :skolemid skolem_user_set_advanced__mapped_set_16
   ))))
   :pattern ((%%apply%%0 (%%lambda%%8 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5 %%hole%%6 %%hole%%7
     ) y$
)))))
(assert
 (=>
  (fuel_bool fuel%set_advanced!mapped_set.)
  (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (s! Poly) (f! Poly)) (!
    (= (set_advanced!mapped_set.? T&. T& U&. U& s! f!) (vstd!set.impl&%0.new.? U&. U& (
       Poly%fun%1. (mk_fun (%%lambda%%8 T&. T& s! T& T&. T& s! (%Poly%fun%1. f!)))
    )))
    :pattern ((set_advanced!mapped_set.? T&. T& U&. U& s! f!))
    :qid internal_set_advanced!mapped_set.?_definition
    :skolemid skolem_internal_set_advanced!mapped_set.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (s! Poly) (f! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. T&. T&))
     (has_type f! (TYPE%fun%1. T&. T& U&. U&))
    )
    (has_type (set_advanced!mapped_set.? T&. T& U&. U& s! f!) (TYPE%vstd!set.Set. U&. U&))
   )
   :pattern ((set_advanced!mapped_set.? T&. T& U&. U& s! f!))
   :qid internal_set_advanced!mapped_set.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!mapped_set.?_pre_post_definition
)))

;; Function-Axioms set_advanced::graph_edges
(assert
 (fuel_bool_default fuel%set_advanced!graph_edges.)
)
(declare-fun %%lambda%%9 () %%Function%%)
(assert
 (forall ((e$ Poly)) (!
   (= (%%apply%%0 %%lambda%%9 e$) (B (=>
      (not (and
        (and
         ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
         ((_ is set_advanced!Node./A) (%Poly%set_advanced!Node. (tuple%2./tuple%2/0 (%Poly%tuple%2.
             e$
        )))))
        ((_ is set_advanced!Node./B) (%Poly%set_advanced!Node. (tuple%2./tuple%2/1 (%Poly%tuple%2.
            e$
      ))))))
      (=>
       (not (and
         (and
          ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
          ((_ is set_advanced!Node./B) (%Poly%set_advanced!Node. (tuple%2./tuple%2/0 (%Poly%tuple%2.
              e$
         )))))
         ((_ is set_advanced!Node./C) (%Poly%set_advanced!Node. (tuple%2./tuple%2/1 (%Poly%tuple%2.
             e$
       ))))))
       (=>
        (not (and
          (and
           ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
           ((_ is set_advanced!Node./C) (%Poly%set_advanced!Node. (tuple%2./tuple%2/0 (%Poly%tuple%2.
               e$
          )))))
          ((_ is set_advanced!Node./D) (%Poly%set_advanced!Node. (tuple%2./tuple%2/1 (%Poly%tuple%2.
              e$
        ))))))
        (and
         (and
          ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
          ((_ is set_advanced!Node./A) (%Poly%set_advanced!Node. (tuple%2./tuple%2/0 (%Poly%tuple%2.
              e$
         )))))
         ((_ is set_advanced!Node./D) (%Poly%set_advanced!Node. (tuple%2./tuple%2/1 (%Poly%tuple%2.
             e$
   ))))))))))
   :pattern ((%%apply%%0 %%lambda%%9 e$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!graph_edges.)
  (forall ((no%param Poly)) (!
    (= (set_advanced!graph_edges.? no%param) (%Poly%vstd!set.Set<tuple%2<set_advanced!Node./set_advanced!Node.>.>.
      (vstd!set.impl&%0.new.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.)
       (Poly%fun%1. (mk_fun %%lambda%%9))
    )))
    :pattern ((set_advanced!graph_edges.? no%param))
    :qid internal_set_advanced!graph_edges.?_definition
    :skolemid skolem_internal_set_advanced!graph_edges.?_definition
))))

;; Function-Axioms set_advanced::neighbors
(assert
 (fuel_bool_default fuel%set_advanced!neighbors.)
)
(declare-fun %%lambda%%10 (Poly Dcr Type Poly Poly Dcr Type Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Poly) (%%hole%%1 Dcr) (%%hole%%2 Type) (%%hole%%3 Poly) (%%hole%%4
    Poly
   ) (%%hole%%5 Dcr) (%%hole%%6 Type) (%%hole%%7 Poly) (m$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%10 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
      %%hole%%6 %%hole%%7
     ) m$
    ) (B (or
      (vstd!set.Set.contains.? %%hole%%1 %%hole%%2 %%hole%%3 (Poly%tuple%2. (tuple%2./tuple%2
         %%hole%%0 m$
      )))
      (vstd!set.Set.contains.? %%hole%%5 %%hole%%6 %%hole%%7 (Poly%tuple%2. (tuple%2./tuple%2
         m$ %%hole%%4
   ))))))
   :pattern ((%%apply%%0 (%%lambda%%10 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5 %%hole%%6 %%hole%%7
     ) m$
)))))
(assert
 (=>
  (fuel_bool fuel%set_advanced!neighbors.)
  (forall ((n! Poly) (graph! Poly)) (!
    (= (set_advanced!neighbors.? n! graph!) (%Poly%vstd!set.Set<set_advanced!Node.>. (vstd!set.impl&%0.new.?
       $ TYPE%set_advanced!Node. (Poly%fun%1. (mk_fun (%%lambda%%10 n! (DST $) (TYPE%tuple%2.
           $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.
          ) graph! n! (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.)
          graph!
    ))))))
    :pattern ((set_advanced!neighbors.? n! graph!))
    :qid internal_set_advanced!neighbors.?_definition
    :skolemid skolem_internal_set_advanced!neighbors.?_definition
))))

;; Function-Axioms set_advanced::is_undirected
(assert
 (fuel_bool_default fuel%set_advanced!is_undirected.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!is_undirected.)
  (forall ((graph! Poly)) (!
    (= (set_advanced!is_undirected.? graph!) (forall ((n1$ Poly) (n2$ Poly)) (!
       (=>
        (and
         (has_type n1$ TYPE%set_advanced!Node.)
         (has_type n2$ TYPE%set_advanced!Node.)
        )
        (=>
         (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.)
          graph! (Poly%tuple%2. (tuple%2./tuple%2 n1$ n2$))
         )
         (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.)
          graph! (Poly%tuple%2. (tuple%2./tuple%2 n2$ n1$))
       )))
       :pattern ((vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node.
          $ TYPE%set_advanced!Node.
         ) graph! (Poly%tuple%2. (tuple%2./tuple%2 n1$ n2$))
       ))
       :pattern ((vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node.
          $ TYPE%set_advanced!Node.
         ) graph! (Poly%tuple%2. (tuple%2./tuple%2 n2$ n1$))
       ))
       :qid user_set_advanced__is_undirected_17
       :skolemid skolem_user_set_advanced__is_undirected_17
    )))
    :pattern ((set_advanced!is_undirected.? graph!))
    :qid internal_set_advanced!is_undirected.?_definition
    :skolemid skolem_internal_set_advanced!is_undirected.?_definition
))))

;; Function-Axioms set_advanced::has_path
(assert
 (fuel_bool_default fuel%set_advanced!has_path.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!has_path.)
  (forall ((graph! Poly) (start! Poly) (end! Poly) (visited! Poly)) (!
    (= (set_advanced!has_path.? graph! start! end! visited!) (or
      (= start! end!)
      (exists ((next$ Poly)) (!
        (and
         (has_type next$ TYPE%set_advanced!Node.)
         (and
          (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node. $ TYPE%set_advanced!Node.)
           graph! (Poly%tuple%2. (tuple%2./tuple%2 start! next$))
          )
          (not (vstd!set.Set.contains.? $ TYPE%set_advanced!Node. visited! start!))
        ))
        :pattern ((vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Node.
           $ TYPE%set_advanced!Node.
          ) graph! (Poly%tuple%2. (tuple%2./tuple%2 start! next$))
        ))
        :qid user_set_advanced__has_path_18
        :skolemid skolem_user_set_advanced__has_path_18
    ))))
    :pattern ((set_advanced!has_path.? graph! start! end! visited!))
    :qid internal_set_advanced!has_path.?_definition
    :skolemid skolem_internal_set_advanced!has_path.?_definition
))))

;; Function-Axioms set_advanced::employee_table
(assert
 (fuel_bool_default fuel%set_advanced!employee_table.)
)
(declare-fun %%lambda%%11 () %%Function%%)
(assert
 (forall ((e$ Poly)) (!
   (= (%%apply%%0 %%lambda%%11 e$) (B (=>
      (not (and
        (and
         ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
         ((_ is set_advanced!Name./Alice) (%Poly%set_advanced!Name. (tuple%2./tuple%2/0 (%Poly%tuple%2.
             e$
        )))))
        ((_ is set_advanced!Department./Engineering)(%Poly%set_advanced!Department. (tuple%2./tuple%2/1
           (%Poly%tuple%2. e$)
      )))))
      (=>
       (not (and
         (and
          ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
          ((_ is set_advanced!Name./Bob) (%Poly%set_advanced!Name. (tuple%2./tuple%2/0 (%Poly%tuple%2.
              e$
         )))))
         ((_ is set_advanced!Department./Sales) (%Poly%set_advanced!Department. (tuple%2./tuple%2/1
            (%Poly%tuple%2. e$)
       )))))
       (=>
        (not (and
          (and
           ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
           ((_ is set_advanced!Name./Carol) (%Poly%set_advanced!Name. (tuple%2./tuple%2/0 (%Poly%tuple%2.
               e$
          )))))
          ((_ is set_advanced!Department./Marketing) (%Poly%set_advanced!Department. (tuple%2./tuple%2/1
             (%Poly%tuple%2. e$)
        )))))
        (and
         (and
          ((_ is tuple%2./tuple%2) (%Poly%tuple%2. e$))
          ((_ is set_advanced!Name./David) (%Poly%set_advanced!Name. (tuple%2./tuple%2/0 (%Poly%tuple%2.
              e$
         )))))
         ((_ is set_advanced!Department./Engineering)(%Poly%set_advanced!Department. (tuple%2./tuple%2/1
            (%Poly%tuple%2. e$)
   )))))))))
   :pattern ((%%apply%%0 %%lambda%%11 e$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!employee_table.)
  (forall ((no%param Poly)) (!
    (= (set_advanced!employee_table.? no%param) (%Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
      (vstd!set.impl&%0.new.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $ TYPE%set_advanced!Department.)
       (Poly%fun%1. (mk_fun %%lambda%%11))
    )))
    :pattern ((set_advanced!employee_table.? no%param))
    :qid internal_set_advanced!employee_table.?_definition
    :skolemid skolem_internal_set_advanced!employee_table.?_definition
))))

;; Function-Axioms set_advanced::employee_names
(assert
 (fuel_bool_default fuel%set_advanced!employee_names.)
)
(declare-fun %%lambda%%12 (Dcr Type Poly Type Dcr Type Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (%%hole%%3 Type) (%%hole%%4
    Dcr
   ) (%%hole%%5 Type) (%%hole%%6 Poly) (n$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%12 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
      %%hole%%6
     ) n$
    ) (B (exists ((d$ Poly)) (!
       (and
        (has_type d$ %%hole%%3)
        (vstd!set.Set.contains.? %%hole%%4 %%hole%%5 %%hole%%6 (Poly%tuple%2. (tuple%2./tuple%2
           n$ d$
       ))))
       :pattern ((vstd!set.Set.contains.? %%hole%%0 %%hole%%1 %%hole%%2 (Poly%tuple%2. (tuple%2./tuple%2
           n$ d$
       ))))
       :qid user_set_advanced__employee_names_19
       :skolemid skolem_user_set_advanced__employee_names_19
   ))))
   :pattern ((%%apply%%0 (%%lambda%%12 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5 %%hole%%6
     ) n$
)))))
(assert
 (=>
  (fuel_bool fuel%set_advanced!employee_names.)
  (forall ((no%param Poly)) (!
    (= (set_advanced!employee_names.? no%param) (%Poly%vstd!set.Set<set_advanced!Name.>.
      (vstd!set.impl&%0.new.? $ TYPE%set_advanced!Name. (Poly%fun%1. (mk_fun (%%lambda%%12
          (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $ TYPE%set_advanced!Department.)
          (Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>. (set_advanced!employee_table.?
            (I 0)
           )
          ) TYPE%set_advanced!Department. (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $
           TYPE%set_advanced!Department.
          ) (Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>. (set_advanced!employee_table.?
            (I 0)
    ))))))))
    :pattern ((set_advanced!employee_names.? no%param))
    :qid internal_set_advanced!employee_names.?_definition
    :skolemid skolem_internal_set_advanced!employee_names.?_definition
))))

;; Function-Axioms set_advanced::engineers
(assert
 (fuel_bool_default fuel%set_advanced!engineers.)
)
(declare-fun %%lambda%%13 (Poly Dcr Type Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Poly) (%%hole%%1 Dcr) (%%hole%%2 Type) (%%hole%%3 Poly) (n$ Poly))
  (!
   (= (%%apply%%0 (%%lambda%%13 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) n$) (B (vstd!set.Set.contains.?
      %%hole%%1 %%hole%%2 %%hole%%3 (Poly%tuple%2. (tuple%2./tuple%2 n$ %%hole%%0))
   )))
   :pattern ((%%apply%%0 (%%lambda%%13 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) n$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!engineers.)
  (forall ((no%param Poly)) (!
    (= (set_advanced!engineers.? no%param) (%Poly%vstd!set.Set<set_advanced!Name.>. (vstd!set.impl&%0.new.?
       $ TYPE%set_advanced!Name. (Poly%fun%1. (mk_fun (%%lambda%%13 (Poly%set_advanced!Department.
           set_advanced!Department./Engineering
          ) (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $ TYPE%set_advanced!Department.)
          (Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>. (set_advanced!employee_table.?
            (I 0)
    ))))))))
    :pattern ((set_advanced!engineers.? no%param))
    :qid internal_set_advanced!engineers.?_definition
    :skolemid skolem_internal_set_advanced!engineers.?_definition
))))

;; Function-Axioms set_advanced::engineering_employees
(assert
 (fuel_bool_default fuel%set_advanced!engineering_employees.)
)
(declare-fun %%lambda%%14 (set_advanced!Department.) %%Function%%)
(assert
 (forall ((%%hole%%0 set_advanced!Department.) (e$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%14 %%hole%%0) e$) (B (= (%Poly%set_advanced!Department. (tuple%2./tuple%2/1
        (%Poly%tuple%2. e$)
       )
      ) %%hole%%0
   )))
   :pattern ((%%apply%%0 (%%lambda%%14 %%hole%%0) e$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!engineering_employees.)
  (forall ((no%param Poly)) (!
    (= (set_advanced!engineering_employees.? no%param) (%Poly%vstd!set.Set<tuple%2<set_advanced!Name./set_advanced!Department.>.>.
      (vstd!set.impl&%0.new.? (DST $) (TYPE%tuple%2. $ TYPE%set_advanced!Name. $ TYPE%set_advanced!Department.)
       (Poly%fun%1. (mk_fun (%%lambda%%14 set_advanced!Department./Engineering)))
    )))
    :pattern ((set_advanced!engineering_employees.? no%param))
    :qid internal_set_advanced!engineering_employees.?_definition
    :skolemid skolem_internal_set_advanced!engineering_employees.?_definition
))))

;; Function-Axioms set_advanced::pair_set
(assert
 (fuel_bool_default fuel%set_advanced!pair_set.)
)
(declare-fun %%lambda%%15 (Poly Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Poly) (%%hole%%1 Poly) (z$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%15 %%hole%%0 %%hole%%1) z$) (B (or
      (= z$ %%hole%%0)
      (= z$ %%hole%%1)
   )))
   :pattern ((%%apply%%0 (%%lambda%%15 %%hole%%0 %%hole%%1) z$))
)))
(assert
 (=>
  (fuel_bool fuel%set_advanced!pair_set.)
  (forall ((T&. Dcr) (T& Type) (x! Poly) (y! Poly)) (!
    (= (set_advanced!pair_set.? T&. T& x! y!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%15 x! y!))
    )))
    :pattern ((set_advanced!pair_set.? T&. T& x! y!))
    :qid internal_set_advanced!pair_set.?_definition
    :skolemid skolem_internal_set_advanced!pair_set.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly) (y! Poly)) (!
   (=>
    (and
     (has_type x! T&)
     (has_type y! T&)
    )
    (has_type (set_advanced!pair_set.? T&. T& x! y!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_advanced!pair_set.? T&. T& x! y!))
   :qid internal_set_advanced!pair_set.?_pre_post_definition
   :skolemid skolem_internal_set_advanced!pair_set.?_pre_post_definition
)))

;; Function-Axioms set_advanced::are_disjoint
(assert
 (fuel_bool_default fuel%set_advanced!are_disjoint.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!are_disjoint.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_advanced!are_disjoint.? T&. T& s1! s2!) (forall ((x$ Poly)) (!
       (=>
        (has_type x$ T&)
        (not (and
          (vstd!set.Set.contains.? T&. T& s1! x$)
          (vstd!set.Set.contains.? T&. T& s2! x$)
       )))
       :pattern ((vstd!set.Set.contains.? T&. T& s1! x$))
       :pattern ((vstd!set.Set.contains.? T&. T& s2! x$))
       :qid user_set_advanced__are_disjoint_20
       :skolemid skolem_user_set_advanced__are_disjoint_20
    )))
    :pattern ((set_advanced!are_disjoint.? T&. T& s1! s2!))
    :qid internal_set_advanced!are_disjoint.?_definition
    :skolemid skolem_internal_set_advanced!are_disjoint.?_definition
))))

;; Function-Axioms set_advanced::are_overlapping
(assert
 (fuel_bool_default fuel%set_advanced!are_overlapping.)
)
(assert
 (=>
  (fuel_bool fuel%set_advanced!are_overlapping.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_advanced!are_overlapping.? T&. T& s1! s2!) (exists ((x$ Poly)) (!
       (and
        (has_type x$ T&)
        (and
         (vstd!set.Set.contains.? T&. T& s1! x$)
         (vstd!set.Set.contains.? T&. T& s2! x$)
       ))
       :pattern ((vstd!set.Set.contains.? T&. T& s1! x$))
       :pattern ((vstd!set.Set.contains.? T&. T& s2! x$))
       :qid user_set_advanced__are_overlapping_21
       :skolemid skolem_user_set_advanced__are_overlapping_21
    )))
    :pattern ((set_advanced!are_overlapping.? T&. T& s1! s2!))
    :qid internal_set_advanced!are_overlapping.?_definition
    :skolemid skolem_internal_set_advanced!are_overlapping.?_definition
))))

;; Function-Specs set_advanced::power_set_membership
(declare-fun ens%set_advanced!power_set_membership. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (subset! Poly) (s! Poly)) (!
   (= (ens%set_advanced!power_set_membership. T&. T& subset! s!) (= (set_advanced!is_member.?
      $ (TYPE%vstd!set.Set. T&. T&) subset! (set_advanced!power_set.? T&. T& s!)
     ) (set_advanced!is_subset.? T&. T& subset! s!)
   ))
   :pattern ((ens%set_advanced!power_set_membership. T&. T& subset! s!))
   :qid internal_ens__set_advanced!power_set_membership._definition
   :skolemid skolem_internal_ens__set_advanced!power_set_membership._definition
)))

;; Function-Def set_advanced::power_set_membership
;; set_advanced.rs:37:7: 37:60 (#0)
(get-info :all-statistics)

 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const x! Poly)
 (declare-const y! Poly)
 (declare-const z! Poly)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type x! T&)
 )
 (assert
  (has_type y! T&)
 )
 (assert
  (has_type z! T&)
 )
 ;; postcondition not satisfied
 (declare-const %%location_label%%0 Bool)
 (assert
  (not (=>
    %%location_label%%0
    (= (set_advanced!is_member.? T&. T& z! (set_advanced!pair_set.? T&. T& x! y!)) (or
      (= z! x!)
      (= z! y!)
 )))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
