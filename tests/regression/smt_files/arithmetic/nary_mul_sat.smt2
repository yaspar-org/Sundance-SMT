(set-logic QF_LIA)
; Issue #256: n-ary products are linear when at most one factor is
; non-constant. (* 2 3 4 x) = 24x and (* 2 (+ y 1) 5) = 10y + 10.
; Model: x = 2, y = -1.
(declare-const x Int)
(declare-const y Int)
(assert (= (* 2 3 4 x) 48))
(assert (= (* 2 (+ y 1) 5) (- x 2)))
(assert (< y 0))
(check-sat)
