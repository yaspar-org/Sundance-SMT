; x = n/2 strictly between 0 and 0.5 needs 0 < n < 1.
(set-logic QF_LIRA)
(declare-const n Int)
(declare-const x Real)
(assert (= x (/ (to_real n) 2.0)))
(assert (< 0.0 x))
(assert (< x 0.5))
(check-sat)
