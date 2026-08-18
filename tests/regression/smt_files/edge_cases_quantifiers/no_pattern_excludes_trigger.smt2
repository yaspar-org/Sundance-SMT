; sundance-flags: --infer-triggers
; `:no-pattern (g x)` forbids (g x) as a trigger, so trigger inference must
; instead pick (f x); it fires on (f 7) and instantiates x := 7 -> unsat.
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (! (=> (p (f x)) (= (g x) 0)) :no-pattern (g x))))
(assert (p (f 7)))
(assert (not (= (g 7) 0)))
(check-sat)
