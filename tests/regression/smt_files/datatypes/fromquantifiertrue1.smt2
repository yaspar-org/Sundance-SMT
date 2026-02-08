(declare-sort P 0)
(declare-datatypes ((i 0)) (((s (b P)))))
(declare-fun o (i) i)
(declare-fun t () i)
(declare-const k i)
;(assert (= k (o k)))
;(assert (= t (o t)))
(assert (not (= t k)))
(assert (= (b t) (b k)))

                ;(assert (=> ((_ is s) t) (= t (s (b t)))))

                ;(assert (=> ((_ is s) k) (= k (s (b k)))))
(check-sat)
