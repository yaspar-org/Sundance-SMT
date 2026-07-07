(set-logic QF_LIA)
; The fundamental axiom holds: x = d * (div x d) + (mod x d)
; With constant divisor d=5, x=17
(declare-fun x () Int)
(assert (= x 17))
(assert (= x (+ (* 5 (div x 5)) (mod x 5))))
(check-sat)
