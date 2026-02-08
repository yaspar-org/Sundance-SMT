(declare-sort z 0)
(declare-fun B (Bool) z)
(declare-const b Bool)
(declare-const v z)
(assert (not (= (B b) v)))
(assert (= v (B (and b true)))) ; note cant simplify to true -> this is the crux of the problem
(check-sat)