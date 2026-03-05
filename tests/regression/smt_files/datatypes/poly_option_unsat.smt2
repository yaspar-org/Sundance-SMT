(declare-sort Val 0)
(declare-datatypes ((Option 1)) ((par (T) ((None) (Some (value T))))))

(declare-const x Val)
(declare-const o (Option Val))

(assert ((_ is None) o))
(assert ((_ is Some) o))

(check-sat)
