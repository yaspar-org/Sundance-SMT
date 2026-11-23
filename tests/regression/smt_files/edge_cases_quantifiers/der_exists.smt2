; Destructive equality resolution on an exists: (exists x. x > 0 and x = y) is (> y 0).
; The exists has no trigger, so without the rewrite it is never instantiated.
(set-logic UFLIA)
(declare-fun y () Int)
(assert (not (exists ((x Int)) (and (> x 0) (= x y)))))
(assert (> y 0))
(check-sat)
