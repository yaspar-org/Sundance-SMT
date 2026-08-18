; Rejection test (issue #52): non-linear multiplication.
; (* x x) has no constant operand, so it cannot be linearized. The internal
; arithmetic solver must reject this rather than silently treating (* x x) as 0.
; (If it collapsed to 0 the query would look unsat via 0 = 4, but the real
; answer is sat: x = 2 or x = -2.)
(set-logic ALL)
(declare-const x Int)
(assert (= (* x x) 4))
(check-sat)
