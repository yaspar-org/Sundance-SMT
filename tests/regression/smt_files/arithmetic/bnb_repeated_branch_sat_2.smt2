(set-logic QF_LIA)
; Branch-and-bound branches on the same variable twice along one path; resolving the
; variable away entirely at the inner node pruned a subtree containing the model.
; Random fuzz seed 8105. Model: x0 = 0, x1 = 2, x2 = 3
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (<= (- 3) x0))
(assert (<= x0 3))
(assert (<= (- 3) x1))
(assert (<= x1 3))
(assert (<= (- 3) x2))
(assert (<= x2 3))
(assert (< (+ (- 2) (* (- 3) x2)) (+ (- 3) (* (- 1) x1) (* (- 2) x1))))
(assert (< (+ (- 1) (* (- 1) x1)) (+ (- 5) (* 3 x1) (* (- 1) x0))))
(assert (or (= (+ 3 (* (- 1) x1)) (+ (- 5) (* 2 x2) (* (- 2) x0) (* 2 (mod x2 3)))) (= (+ (- 3) (* 1 x1)) (+ 5 (* 1 x2) (* 2 (mod x1 3))))))
(check-sat)
