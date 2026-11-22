(set-logic QF_LIA)
; Issue #256: variable in the middle of an n-ary product, with a negative
; and a nested constant factor. (* 2 x (- 1) (* 1 3)) = -6x; -6x = 13 has
; no integer solution.
(declare-const x Int)
(assert (= (* 2 x (- 1) (* 1 3)) 13))
(check-sat)
