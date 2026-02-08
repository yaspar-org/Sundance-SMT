(declare-sort S 0)
(declare-const x Bool)
(declare-const A S)
(declare-const B S)

(assert (not (or (= (ite x A B) A) (= (ite x A B) B))))
(check-sat)