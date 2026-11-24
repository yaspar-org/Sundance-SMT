; Arithmetic implies x = y, which the e-graph needs to refute f(x) != f(y).
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (<= x y))
(assert (<= y x))
(assert (not (= (f x) (f y))))
(check-sat)
