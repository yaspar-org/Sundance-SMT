(set-logic ALL)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)

(assert
  (forall ((x U))
    (! (=> (p x) (q x))
       :pattern ((p x)))))

; Deliberately register the goal-distant match first.
(assert (p b))
(assert (p a))

; Sundance's goal-based mode treats the final assertion as the goal.
(assert (not (q a)))
(check-sat)
