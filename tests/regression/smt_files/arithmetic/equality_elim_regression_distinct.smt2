(declare-fun n () Int)
(assert (= 5 (+ n 1)))
(assert (distinct n 4))
(check-sat)
