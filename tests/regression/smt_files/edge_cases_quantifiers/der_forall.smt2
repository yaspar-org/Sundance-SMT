; Destructive equality resolution: the forall has no trigger, but x is defined by
; x = y + 1, so it reduces to the ground (= (+ y 1) 19).
(set-logic UFLIA)
(declare-fun y () Int)
(assert (forall ((x Int)) (=> (= x (+ y 1)) (= x 19))))
(assert (not (= y 18)))
(check-sat)
