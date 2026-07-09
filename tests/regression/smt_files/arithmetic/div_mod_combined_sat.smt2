(set-logic QF_LIA)
; Find x such that div x 4 = 3 and mod x 4 = 1 -> x = 13
(declare-fun x () Int)
(assert (= (div x 4) 3))
(assert (= (mod x 4) 1))
(assert (= x 13))
(check-sat)
