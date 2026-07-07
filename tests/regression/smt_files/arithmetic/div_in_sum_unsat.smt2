(set-logic QF_LIA)
; (div 10 3) + (div 10 3) = 6
(declare-fun x () Int)
(assert (= x (+ (div 10 3) (div 10 3))))
(assert (not (= x 6)))
(check-sat)
