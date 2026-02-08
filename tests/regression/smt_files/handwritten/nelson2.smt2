; another cool example from the original congruence closure paper
; should be unsat

(set-logic QF_UF)
(declare-sort T 0)
(declare-sort S 0)
(declare-fun x () T)
(declare-fun y () T)
(declare-fun f (T T) T)
(assert (= true false))
(assert false)
(assert (= (f x y) x))
(assert (not (= (f (f x y) y) x)))
(check-sat)