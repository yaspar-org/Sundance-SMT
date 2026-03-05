; Test nested ADT satisfiable case
(declare-sort Value 0)
(declare-datatypes ((Option 1)(Result 1))((par (T)((None)(Some (value T))))(par (T)((Ok (ok-value (Option T)))(Err (err-msg T))))))

(declare-const v1 Value)
(declare-const v2 Value)
(declare-const opt (Option Value))
(declare-const res (Result Value))

; Satisfiable nested structure
(assert
        (= opt (Some v1)))
(assert
        (= res (Ok opt)))

; Test nested access
(assert
        (= (value (ok-value res)) v1))
(assert
        ((_ is Some) (ok-value res)))
(assert
        ((_ is Ok) res))

; Additional constraints that should be satisfiable
(assert
        (not (= v1 v2)))
(assert
        (not ((_ is None) opt)))
(assert
        (not ((_ is Err) res)))

(check-sat)
