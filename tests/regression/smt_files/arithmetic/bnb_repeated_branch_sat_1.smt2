(set-logic QF_LIA)
; Branch-and-bound branches on the same variable twice along one path; resolving the
; variable away entirely at the inner node pruned a subtree containing the model.
; Random fuzz seed 7392. Model: x0 = 0, x1 = 3, x2 = 0
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (<= (- 3) x0))
(assert (<= x0 3))
(assert (<= (- 3) x1))
(assert (<= x1 3))
(assert (<= (- 3) x2))
(assert (<= x2 3))
(assert (< (+ 4 (* 1 (mod x0 3))) (+ 4 (* 2 (div x1 3)))))
(assert (not (< (+ (- 2) (* (- 3) x2) (* 2 x1)) (+ 2 (* (- 1) x1) (* 1 x2)))))
(check-sat)
