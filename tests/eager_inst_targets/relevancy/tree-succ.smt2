(declare-fun l(Int) Int)
(declare-fun r(Int) Int)
(declare-fun P(Int Int) Bool)

(declare-fun succ(Int) Int)

(define-fun tree_depth() Int 
    (succ (succ (succ (succ (succ
    0))))))

(assert (forall ((x Int) (d Int)) 
(!
    (=> (P x d)
        (or 
            (P (l x) (succ d))
            (P (r x) (succ d))
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


