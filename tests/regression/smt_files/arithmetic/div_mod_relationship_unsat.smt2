(set-logic QF_LIA)
; The fundamental axiom: x = d * (div x d) + (mod x d)
; With constant divisor d=5, x=17: 17 = 5*3 + 2
; Test that div and mod are consistent
(declare-fun x () Int)
(assert (= x 17))
(assert (not (= x (+ (* 5 (div x 5)) (mod x 5)))))
(check-sat)
