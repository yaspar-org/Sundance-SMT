; (/ (+ y 1) 2) = 0.75 forces y = 0.5; then 3 * y / 1.5 = 1.
(set-logic QF_LRA)
(declare-const y Real)
(assert (= (/ (+ y 1) 2) 0.75))
(assert (distinct (/ (* 3 y) 1.5) 1))
(check-sat)
