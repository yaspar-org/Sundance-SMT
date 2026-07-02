(set-logic QF_LIA)
; SMT-LIB mod is always non-negative:
; mod (-7) 2 = 1 (since -7 = 2*(-4) + 1)
(declare-fun x () Int)
(assert (= x (mod (- 7) 2)))
(assert (not (= x 1)))
(check-sat)
