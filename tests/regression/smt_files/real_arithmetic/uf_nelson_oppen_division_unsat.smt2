; Arithmetic implies x = 0.75; f(x) and f(0.75) must then agree.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (= (* 2 x) (+ y 1)))
(assert (= (/ (+ y 1) 2) 0.75))
(assert (not (= (f x) (f 0.75))))
(check-sat)
