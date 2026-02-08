(assert (forall ((x Int)) (! (< (+ x 0) 5) :pattern ((+ x 0)))))

(assert (= (+ 6 0) (+ 5 1)))
(check-sat)