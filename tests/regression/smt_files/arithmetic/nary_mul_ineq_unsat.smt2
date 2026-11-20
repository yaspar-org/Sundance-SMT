(set-logic QF_LIA)
; Issue #256: n-ary product inside an inequality atom (constraint path).
; x >= 1 implies (* x 2 3) = 6x >= 6 > 5.
(declare-const x Int)
(assert (>= x 1))
(assert (<= (* x 2 3) 5))
(check-sat)
