; No :pattern given; trigger inference selects (p x), which fires on (p 5).
(set-logic ALL)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (not (p 5)))
(check-sat)
