(set-logic QF_LIA)
; Issue #256: n-ary product (* 2 3 x) was left unconstrained by the
; incremental arithmetic backend. 6x = 12 forces x = 2.
(declare-const x Int)
(assert (= (* 2 3 x) 12))
(assert (not (= x 2)))
(check-sat)
