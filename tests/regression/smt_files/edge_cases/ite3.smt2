(declare-fun y () Bool)
(assert (= y (ite false false false)))
(assert y)
(check-sat)
