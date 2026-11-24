; Strict bounds leave an open interval; the disjunction forces a point in it.
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (< (+ x y) 1))
(assert (> (- x y) 0.5))
(assert (>= y 0))
(assert (or (> x 0.9) (< y 0.1)))
(check-sat)
