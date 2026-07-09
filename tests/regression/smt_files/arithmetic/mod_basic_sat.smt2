(set-logic QF_LIA)
; mod 10 3 = 1
(declare-fun x () Int)
(assert (= x (mod 10 3)))
(assert (= x 1))
(check-sat)
