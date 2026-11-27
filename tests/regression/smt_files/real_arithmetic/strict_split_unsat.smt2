; x is pinned to 0.5 by non-strict bounds, so neither strict side holds.
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 0.5))
(assert (<= x (/ 1 2)))
(assert (or (< x 0.5) (> x 0.5)))
(check-sat)
