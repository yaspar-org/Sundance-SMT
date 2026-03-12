(declare-fun f (Int) Int)
(assert (and (= (f 0) (+ 1 (f 1))) (ite true true (= (f 0) (+ 1 (f 0)))) (or true (= 0 1))))
(check-sat)
