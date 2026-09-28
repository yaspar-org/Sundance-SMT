(declare-fun l(Int) Int)
(declare-fun r(Int) Int)
(declare-fun P(Int Int) Bool)

(define-fun tree_depth() Int 5)

(assert (forall ((x Int) (d Int)) 
(!
    (=> (P x d)
        (or 
            (P (l x) (+ d 1))
            (P (r x) (+ d 1))
        )
    )
    :pattern ((P x d))
)))

(assert (forall ((x Int))
(!
    (and 
        (P x tree_depth)
        (not (P 0 0))
        (not (P 1 0))
    )
    :pattern ((P x tree_depth))
)))

(assert (or (P 0 0) (P 1 0)))

(check-sat)


