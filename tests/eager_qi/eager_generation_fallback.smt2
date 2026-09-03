(set-logic ALL)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-const a U)

(assert (forall ((x U)) (! (=> (p x) (p (f x))) :pattern ((p x)))))
(assert (p a))
(assert (not (p (f (f a)))))

(check-sat)
