(set-logic QF_LIA)
; (- 1 0 0) = 1, so (= 1 (- 1 0 0)) is sat
(assert (= 1 (- 1 0 0)))
(check-sat)
