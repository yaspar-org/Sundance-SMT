; The tester (_ is C) and the function |(is C)| are different symbols: congruence must not merge them.
(declare-datatype D ((C) (E)))
(declare-fun |(is C)| (D) Bool)
(declare-const x D)
(assert ((_ is C) x))
(assert (not (|(is C)| x)))
(check-sat)
