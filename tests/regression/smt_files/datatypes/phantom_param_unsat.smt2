; Parametric datatype with a PHANTOM type parameter: `T` appears in no field of any
; constructor, so an applied constructor `(mk ...)` cannot have `T` inferred from its
; arguments and must be printed with an explicit sort ascription. Regression guard for
; parametric-constructor sort ascription (both nullary and applied constructors).
(declare-sort Val 0)
(declare-datatypes ((Box 1)) ((par (T) ((mk (v Int))))))
(declare-const b1 (Box Val))
(declare-const b2 (Box Val))
(assert (= (v b1) (v b2)))
(assert (not (= b1 b2)))
(check-sat)
