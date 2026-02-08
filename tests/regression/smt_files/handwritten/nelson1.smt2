; cool example from the original congruence closure paper
; should be unsat

(set-logic QF_UF)
(declare-sort T 0)
(declare-sort S 0)
(declare-fun x () T)
(declare-fun f (T) T)
(assert (= (f (f (f x))) x))
(assert (= (f (f (f (f (f x))))) x))
(assert (not (= (f x) x)))
(check-sat)