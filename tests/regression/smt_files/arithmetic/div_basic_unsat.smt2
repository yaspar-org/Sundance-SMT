(set-logic QF_LIA)
; div 0 1 = 0, not 1
(declare-fun x () Int)
(assert (= x (div 0 1)))
(assert (= x 1))
(check-sat)
