(set-logic ALL)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)

(assert (forall ((x U)) (! (= (f x) x) :pattern ((f x)))))
(assert (distinct (f a) a))

(check-sat)
