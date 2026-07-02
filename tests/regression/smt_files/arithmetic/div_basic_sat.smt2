(set-logic QF_LIA)
; div 10 3 = 3
(declare-fun x () Int)
(assert (= x (div 10 3)))
(assert (= x 3))
(check-sat)
