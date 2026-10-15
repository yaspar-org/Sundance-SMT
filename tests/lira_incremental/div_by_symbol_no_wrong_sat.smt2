; Unsat: div(3, 2) = 1, not 5. The divisor is a symbol, so the incremental internal backend
; treats div(x, y) as an opaque integer and finds a "model" with div(x, y) = 5. That model is not
; a model of the input, so the answer must be unknown (or unsat), never sat.
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (= x 3))
(assert (= y 2))
(assert (= (div x y) 5))
(check-sat)
