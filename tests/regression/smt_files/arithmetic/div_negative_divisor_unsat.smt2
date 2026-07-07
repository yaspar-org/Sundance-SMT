(set-logic QF_LIA)
; div 10 (- 3) = -3, not -4
(declare-fun x () Int)
(assert (= x (div 10 (- 3))))
(assert (= x (- 4)))
(check-sat)
