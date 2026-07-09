(set-logic QF_LIA)
; mod 10 (- 3) = 1, not 2
(declare-fun x () Int)
(assert (= x (mod 10 (- 3))))
(assert (= x 2))
(check-sat)
