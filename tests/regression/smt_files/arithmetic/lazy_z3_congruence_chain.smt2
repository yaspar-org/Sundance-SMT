; Stress test for lazy Z3 arithmetic interacting with congruence closure.
; Chain: v1=v2, v2=v3, v3=v4 forces f(v1)=f(v2)=f(v3)=f(v4) via congruence.
; Ground fact f(v1)=5 combined with an arithmetic contradiction on f(v4)
; requires the lazy backend to see the full chain of merges asserted into Z3.
(set-logic QF_UFLIA)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun v3 () Int)
(declare-fun v4 () Int)
(declare-fun f (Int) Int)
(assert (= v1 v2))
(assert (= v2 v3))
(assert (= v3 v4))
(assert (= (f v1) 5))
(assert (> (f v4) 5))
(check-sat)
