; `rem` is a valid user-declared function name, not an interpreted IR operator.
(set-logic ALL)
(declare-fun rem (Int) Bool)
(assert (forall ((x Int)) (rem x)))
(assert (not (rem 1)))
(check-sat)
