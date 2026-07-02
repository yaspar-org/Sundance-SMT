(set-logic QF_LIA)
; SMT-LIB div floors towards negative infinity:
; div (-7) 2 = -4 (since -7 = 2*(-4) + 1, remainder 1 >= 0)
(declare-fun x () Int)
(assert (= x (div (- 7) 2)))
(assert (not (= x (- 4))))
(check-sat)
