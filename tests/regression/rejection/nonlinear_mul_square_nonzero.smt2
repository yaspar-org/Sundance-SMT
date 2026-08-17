; Rejection test (issue #52): non-linear multiplication.
; (* x x) has no constant operand, so it cannot be linearized. The internal
; arithmetic solver must reject this rather than silently treating (* x x) as 0.
; (If it collapsed to 0 the query would look sat via 0 = 0, but the real answer
; is unsat: x*x = 0 forces x = 0, contradicting x != 0.)
(set-logic ALL)
(declare-const x Int)
(assert (= (* x x) 0))
(assert (not (= x 0)))
(check-sat)
