(declare-sort Val 0)
(declare-datatypes ((Option 1)) ((par (T) ((None) (Some (value T))))))

(declare-const x Val)
(declare-const y Val)
(declare-const o (Option Val))

(assert (= o (Some x)))
(assert (not (= x y)))

(check-sat)
