(set-logic QF_LIA)
(declare-const var_1 Int)
(declare-const var_13 Int)
(declare-const var_3 Int)
(declare-const var_7 Int)
(assert (= var_13 (+ 0 (* 1 var_3) 1)))   ; v_13 = v_3 + 1
(assert (= var_3 (+ 0 (* 1 var_3) 0)))    ; v_3  = v_3
(assert (= var_1 (+ 0 1)))                ; v_1 = 1
(assert (= var_7 (+ 0 4)))                ; v_7 = 4
(assert (= (+ 0 (* 1 var_3) 1) (+ 0 5)))  ; v_3 = 4 --> after substitution, generates conflict with v_3 < 4
(assert (< (+ 0 (* 1 var_3) 0) (+ 0 4)))  ; v_3 < 4
(assert (< (+ 0 4) (+ 0 (* 1 var_3) 0)))  ; v_3 > 4
(check-sat)
