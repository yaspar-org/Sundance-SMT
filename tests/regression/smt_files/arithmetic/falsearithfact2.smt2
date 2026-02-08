(declare-fun A () Int)
(assert (= (ite true 1 0) A))
(assert (= 0 A))
(check-sat)
