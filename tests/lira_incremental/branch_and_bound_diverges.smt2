; x is even and odd: unsat over the integers, but feasible and unbounded over the rationals, and
; each equality is tight on its own, so integer tightening does not refute it. Branch-and-bound
; runs off along the unbounded direction forever. It runs inside a CaDiCaL callback, so it must
; check `--timeout` itself.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const a Int)
(declare-const b Int)
(assert (= x (* 2 a)))
(assert (= x (+ (* 2 b) 1)))
(check-sat)
