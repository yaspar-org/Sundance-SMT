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
(declare-const fuel%set_simple!is_member. FuelId)
(declare-const fuel%set_simple!set_union. FuelId)
(declare-const fuel%set_simple!set_intersection. FuelId)
(declare-const fuel%set_simple!set_difference. FuelId)
(declare-const fuel%set_simple!set_complement. FuelId)
(declare-const fuel%set_simple!is_subset. FuelId)
(declare-const fuel%set_simple!is_proper_subset. FuelId)
(declare-const fuel%set_simple!set_equality. FuelId)
(declare-const fuel%set_simple!empty_set. FuelId)
(declare-const fuel%set_simple!universal_set. FuelId)
(declare-const fuel%set_simple!singleton. FuelId)
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
  fuel%set_simple!is_member. fuel%set_simple!set_union. fuel%set_simple!set_intersection.
  fuel%set_simple!set_difference. fuel%set_simple!set_complement. fuel%set_simple!is_subset.
  fuel%set_simple!is_proper_subset. fuel%set_simple!set_equality. fuel%set_simple!empty_set.
  fuel%set_simple!universal_set. fuel%set_simple!singleton. fuel%vstd!array.group_array_axioms.
  fuel%vstd!function.group_function_axioms. fuel%vstd!layout.group_layout_axioms. fuel%vstd!map.group_map_axioms.
  fuel%vstd!multiset.group_multiset_axioms. fuel%vstd!raw_ptr.group_raw_ptr_axioms.
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
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-fun TYPE%fun%1. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
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

;; Function-Decl vstd::set::Set::contains
(declare-fun vstd!set.Set.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::set::impl&%0::new
(declare-fun vstd!set.impl&%0.new.? (Dcr Type Poly) Poly)

;; Function-Decl set_simple::is_member
(declare-fun set_simple!is_member.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_simple::set_union
(declare-fun set_simple!set_union.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_simple::set_intersection
(declare-fun set_simple!set_intersection.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_simple::set_difference
(declare-fun set_simple!set_difference.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_simple::set_complement
(declare-fun set_simple!set_complement.? (Dcr Type Poly Poly) Poly)

;; Function-Decl set_simple::is_subset
(declare-fun set_simple!is_subset.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_simple::is_proper_subset
(declare-fun set_simple!is_proper_subset.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_simple::set_equality
(declare-fun set_simple!set_equality.? (Dcr Type Poly Poly) Bool)

;; Function-Decl set_simple::empty_set
(declare-fun set_simple!empty_set.? (Dcr Type) Poly)

;; Function-Decl set_simple::universal_set
(declare-fun set_simple!universal_set.? (Dcr Type Poly) Poly)

;; Function-Decl set_simple::singleton
(declare-fun set_simple!singleton.? (Dcr Type Poly) Poly)

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

;; Function-Axioms set_simple::is_member
(assert
 (fuel_bool_default fuel%set_simple!is_member.)
)
(assert
 (=>
  (fuel_bool fuel%set_simple!is_member.)
  (forall ((T&. Dcr) (T& Type) (x! Poly) (set! Poly)) (!
    (= (set_simple!is_member.? T&. T& x! set!) (vstd!set.Set.contains.? T&. T& set! x!))
    :pattern ((set_simple!is_member.? T&. T& x! set!))
    :qid internal_set_simple!is_member.?_definition
    :skolemid skolem_internal_set_simple!is_member.?_definition
))))

;; Function-Axioms set_simple::set_union
(assert
 (fuel_bool_default fuel%set_simple!set_union.)
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
  (fuel_bool fuel%set_simple!set_union.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_simple!set_union.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%0 T&. T& s1! T&. T& s2!))
    )))
    :pattern ((set_simple!set_union.? T&. T& s1! s2!))
    :qid internal_set_simple!set_union.?_definition
    :skolemid skolem_internal_set_simple!set_union.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_simple!set_union.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_simple!set_union.? T&. T& s1! s2!))
   :qid internal_set_simple!set_union.?_pre_post_definition
   :skolemid skolem_internal_set_simple!set_union.?_pre_post_definition
)))

;; Function-Axioms set_simple::set_intersection
(assert
 (fuel_bool_default fuel%set_simple!set_intersection.)
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
  (fuel_bool fuel%set_simple!set_intersection.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_simple!set_intersection.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%1 T&. T& s1! T&. T& s2!))
    )))
    :pattern ((set_simple!set_intersection.? T&. T& s1! s2!))
    :qid internal_set_simple!set_intersection.?_definition
    :skolemid skolem_internal_set_simple!set_intersection.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_simple!set_intersection.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_simple!set_intersection.? T&. T& s1! s2!))
   :qid internal_set_simple!set_intersection.?_pre_post_definition
   :skolemid skolem_internal_set_simple!set_intersection.?_pre_post_definition
)))

;; Function-Axioms set_simple::set_difference
(assert
 (fuel_bool_default fuel%set_simple!set_difference.)
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
  (fuel_bool fuel%set_simple!set_difference.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_simple!set_difference.? T&. T& s1! s2!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1.
       (mk_fun (%%lambda%%2 T&. T& s1! T&. T& s2!))
    )))
    :pattern ((set_simple!set_difference.? T&. T& s1! s2!))
    :qid internal_set_simple!set_difference.?_definition
    :skolemid skolem_internal_set_simple!set_difference.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. T&. T&))
     (has_type s2! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_simple!set_difference.? T&. T& s1! s2!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_simple!set_difference.? T&. T& s1! s2!))
   :qid internal_set_simple!set_difference.?_pre_post_definition
   :skolemid skolem_internal_set_simple!set_difference.?_pre_post_definition
)))

;; Function-Axioms set_simple::set_complement
(assert
 (fuel_bool_default fuel%set_simple!set_complement.)
)
(assert
 (=>
  (fuel_bool fuel%set_simple!set_complement.)
  (forall ((T&. Dcr) (T& Type) (set! Poly) (universe! Poly)) (!
    (= (set_simple!set_complement.? T&. T& set! universe!) (vstd!set.impl&%0.new.? T&.
      T& (Poly%fun%1. (mk_fun (%%lambda%%2 T&. T& universe! T&. T& set!)))
    ))
    :pattern ((set_simple!set_complement.? T&. T& set! universe!))
    :qid internal_set_simple!set_complement.?_definition
    :skolemid skolem_internal_set_simple!set_complement.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (set! Poly) (universe! Poly)) (!
   (=>
    (and
     (has_type set! (TYPE%vstd!set.Set. T&. T&))
     (has_type universe! (TYPE%vstd!set.Set. T&. T&))
    )
    (has_type (set_simple!set_complement.? T&. T& set! universe!) (TYPE%vstd!set.Set. T&.
      T&
   )))
   :pattern ((set_simple!set_complement.? T&. T& set! universe!))
   :qid internal_set_simple!set_complement.?_pre_post_definition
   :skolemid skolem_internal_set_simple!set_complement.?_pre_post_definition
)))

;; Function-Axioms set_simple::is_subset
(assert
 (fuel_bool_default fuel%set_simple!is_subset.)
)
(assert
 (=>
  (fuel_bool fuel%set_simple!is_subset.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_simple!is_subset.? T&. T& s1! s2!) (forall ((x$ Poly)) (!
       (=>
        (has_type x$ T&)
        (=>
         (vstd!set.Set.contains.? T&. T& s1! x$)
         (vstd!set.Set.contains.? T&. T& s2! x$)
       ))
       :pattern ((vstd!set.Set.contains.? T&. T& s1! x$))
       :pattern ((vstd!set.Set.contains.? T&. T& s2! x$))
       :qid user_set_simple__is_subset_4
       :skolemid skolem_user_set_simple__is_subset_4
    )))
    :pattern ((set_simple!is_subset.? T&. T& s1! s2!))
    :qid internal_set_simple!is_subset.?_definition
    :skolemid skolem_internal_set_simple!is_subset.?_definition
))))

;; Function-Axioms set_simple::is_proper_subset
(assert
 (fuel_bool_default fuel%set_simple!is_proper_subset.)
)
(assert
 (=>
  (fuel_bool fuel%set_simple!is_proper_subset.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_simple!is_proper_subset.? T&. T& s1! s2!) (and
      (set_simple!is_subset.? T&. T& s1! s2!)
      (not (= s1! s2!))
    ))
    :pattern ((set_simple!is_proper_subset.? T&. T& s1! s2!))
    :qid internal_set_simple!is_proper_subset.?_definition
    :skolemid skolem_internal_set_simple!is_proper_subset.?_definition
))))

;; Function-Axioms set_simple::set_equality
(assert
 (fuel_bool_default fuel%set_simple!set_equality.)
)
(assert
 (=>
  (fuel_bool fuel%set_simple!set_equality.)
  (forall ((T&. Dcr) (T& Type) (s1! Poly) (s2! Poly)) (!
    (= (set_simple!set_equality.? T&. T& s1! s2!) (forall ((x$ Poly)) (!
       (=>
        (has_type x$ T&)
        (= (vstd!set.Set.contains.? T&. T& s1! x$) (vstd!set.Set.contains.? T&. T& s2! x$))
       )
       :pattern ((vstd!set.Set.contains.? T&. T& s1! x$))
       :pattern ((vstd!set.Set.contains.? T&. T& s2! x$))
       :qid user_set_simple__set_equality_5
       :skolemid skolem_user_set_simple__set_equality_5
    )))
    :pattern ((set_simple!set_equality.? T&. T& s1! s2!))
    :qid internal_set_simple!set_equality.?_definition
    :skolemid skolem_internal_set_simple!set_equality.?_definition
))))

;; Function-Axioms set_simple::empty_set
(assert
 (fuel_bool_default fuel%set_simple!empty_set.)
)
(declare-fun %%lambda%%3 (Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Poly) (x$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%3 %%hole%%0) x$) %%hole%%0)
   :pattern ((%%apply%%0 (%%lambda%%3 %%hole%%0) x$))
)))
(assert
 (=>
  (fuel_bool fuel%set_simple!empty_set.)
  (forall ((T&. Dcr) (T& Type)) (!
    (= (set_simple!empty_set.? T&. T&) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun
        (%%lambda%%3 (B false))
    ))))
    :pattern ((set_simple!empty_set.? T&. T&))
    :qid internal_set_simple!empty_set.?_definition
    :skolemid skolem_internal_set_simple!empty_set.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (has_type (set_simple!empty_set.? T&. T&) (TYPE%vstd!set.Set. T&. T&))
   :pattern ((set_simple!empty_set.? T&. T&))
   :qid internal_set_simple!empty_set.?_pre_post_definition
   :skolemid skolem_internal_set_simple!empty_set.?_pre_post_definition
)))

;; Function-Axioms set_simple::universal_set
(assert
 (fuel_bool_default fuel%set_simple!universal_set.)
)
(assert
 (=>
  (fuel_bool fuel%set_simple!universal_set.)
  (forall ((T&. Dcr) (T& Type) (universe! Poly)) (!
    (= (set_simple!universal_set.? T&. T& universe!) universe!)
    :pattern ((set_simple!universal_set.? T&. T& universe!))
    :qid internal_set_simple!universal_set.?_definition
    :skolemid skolem_internal_set_simple!universal_set.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (universe! Poly)) (!
   (=>
    (has_type universe! (TYPE%vstd!set.Set. T&. T&))
    (has_type (set_simple!universal_set.? T&. T& universe!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_simple!universal_set.? T&. T& universe!))
   :qid internal_set_simple!universal_set.?_pre_post_definition
   :skolemid skolem_internal_set_simple!universal_set.?_pre_post_definition
)))

;; Function-Axioms set_simple::singleton
(assert
 (fuel_bool_default fuel%set_simple!singleton.)
)
(declare-fun %%lambda%%4 (Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Poly) (y$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%4 %%hole%%0) y$) (B (= y$ %%hole%%0)))
   :pattern ((%%apply%%0 (%%lambda%%4 %%hole%%0) y$))
)))
(assert
 (=>
  (fuel_bool fuel%set_simple!singleton.)
  (forall ((T&. Dcr) (T& Type) (x! Poly)) (!
    (= (set_simple!singleton.? T&. T& x!) (vstd!set.impl&%0.new.? T&. T& (Poly%fun%1. (mk_fun
        (%%lambda%%4 x!)
    ))))
    :pattern ((set_simple!singleton.? T&. T& x!))
    :qid internal_set_simple!singleton.?_definition
    :skolemid skolem_internal_set_simple!singleton.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly)) (!
   (=>
    (has_type x! T&)
    (has_type (set_simple!singleton.? T&. T& x!) (TYPE%vstd!set.Set. T&. T&))
   )
   :pattern ((set_simple!singleton.? T&. T& x!))
   :qid internal_set_simple!singleton.?_pre_post_definition
   :skolemid skolem_internal_set_simple!singleton.?_pre_post_definition
)))

;; Function-Specs set_simple::subset_reflexivity
(declare-fun ens%set_simple!subset_reflexivity. (Dcr Type Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (s! Poly)) (!
   (= (ens%set_simple!subset_reflexivity. T&. T& s!) (set_simple!is_subset.? T&. T& s!
     s!
   ))
   :pattern ((ens%set_simple!subset_reflexivity. T&. T& s!))
   :qid internal_ens__set_simple!subset_reflexivity._definition
   :skolemid skolem_internal_ens__set_simple!subset_reflexivity._definition
)))

;; Function-Def set_simple::subset_reflexivity
;; set_simple.rs:65:7: 65:42 (#0)
(get-info :all-statistics)

;; Function-Specs set_simple::singleton_cardinality
(declare-fun ens%set_simple!singleton_cardinality. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly) (y! Poly)) (!
   (= (ens%set_simple!singleton_cardinality. T&. T& x! y!) (= (set_simple!is_member.? T&.
      T& y! (set_simple!singleton.? T&. T& x!)
     ) (= y! x!)
   ))
   :pattern ((ens%set_simple!singleton_cardinality. T&. T& x! y!))
   :qid internal_ens__set_simple!singleton_cardinality._definition
   :skolemid skolem_internal_ens__set_simple!singleton_cardinality._definition
)))

;; Function-Def set_simple::singleton_cardinality
;; set_simple.rs:83:7: 83:46 (#0)
(get-info :all-statistics)

;; Function-Specs set_simple::empty_set_cardinality
(declare-fun ens%set_simple!empty_set_cardinality. (Dcr Type Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly)) (!
   (= (ens%set_simple!empty_set_cardinality. T&. T& x!) (not (set_simple!is_member.? T&.
      T& x! (set_simple!empty_set.? T&. T&)
   )))
   :pattern ((ens%set_simple!empty_set_cardinality. T&. T& x!))
   :qid internal_ens__set_simple!empty_set_cardinality._definition
   :skolemid skolem_internal_ens__set_simple!empty_set_cardinality._definition
)))

;; Function-Def set_simple::empty_set_cardinality
;; set_simple.rs:91:7: 91:40 (#0)
(get-info :all-statistics)

;; Function-Specs set_simple::self_subset
(declare-fun ens%set_simple!self_subset. (Dcr Type Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (s! Poly)) (!
   (= (ens%set_simple!self_subset. T&. T& s!) (set_simple!is_subset.? T&. T& s! s!))
   :pattern ((ens%set_simple!self_subset. T&. T& s!))
   :qid internal_ens__set_simple!self_subset._definition
   :skolemid skolem_internal_ens__set_simple!self_subset._definition
)))

;; Function-Def set_simple::self_subset
;; set_simple.rs:101:7: 101:35 (#0)
(get-info :all-statistics)

;; Function-Specs set_simple::empty_subset_of_all
(declare-fun ens%set_simple!empty_subset_of_all. (Dcr Type Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (s! Poly)) (!
   (= (ens%set_simple!empty_subset_of_all. T&. T& s!) (set_simple!is_subset.? T&. T& (
      set_simple!empty_set.? T&. T&
     ) s!
   ))
   :pattern ((ens%set_simple!empty_subset_of_all. T&. T& s!))
   :qid internal_ens__set_simple!empty_subset_of_all._definition
   :skolemid skolem_internal_ens__set_simple!empty_subset_of_all._definition
)))

;; Function-Def set_simple::empty_subset_of_all
;; set_simple.rs:109:7: 109:43 (#0)
(get-info :all-statistics)

;; Function-Def set_simple::main
;; set_simple.rs:116:1: 116:10 (#0)
(get-info :all-statistics)

