(declare-sort S 0)
(declare-fun x () S)
(assert (not (= x x)))
(check-sat)
