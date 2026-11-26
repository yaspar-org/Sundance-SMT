; No trigger can be inferred for the forall (its body is pure arithmetic), so it
; is never instantiated; the ground part is satisfiable, so the answer is unknown.
(set-logic UFLIA)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (forall ((x Int)) (or (> x y) (< (+ x x) z))))
(assert (< y z))
(check-sat)
