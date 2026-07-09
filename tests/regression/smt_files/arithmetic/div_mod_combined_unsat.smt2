(set-logic QF_LIA)
; No x satisfies div x 4 = 3 and mod x 4 = 1 and x = 14
; (14 / 4 = 3, 14 mod 4 = 2, not 1)
(declare-fun x () Int)
(assert (= (div x 4) 3))
(assert (= (mod x 4) 1))
(assert (= x 14))
(check-sat)
