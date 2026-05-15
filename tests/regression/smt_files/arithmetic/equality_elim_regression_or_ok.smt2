(declare-fun n () Int)
(assert (= 5 (+ n 1)))
(assert (or (< n 4) (> n 4)))
(check-sat)
