; Stress test for incremental Z3 with deeply nested arithmetic and late-arriving merges.
; Two nested chains that only become contradictory once the merge x = y is
; asserted. Each `+`-app has a definitional pinning in Z3 (var == var_child+1),
; so the merge must propagate through several levels to expose the conflict.
(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ (+ (+ x 1) 1) 1) 10))
(assert (= (+ (+ (+ y 1) 1) 1) 20))
(assert (= x y))
(check-sat)
