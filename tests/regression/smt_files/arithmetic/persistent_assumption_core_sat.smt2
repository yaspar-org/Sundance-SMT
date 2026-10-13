; Satisfiable, e.g. x = y = 0 and p = true. The incremental Z3 backend once
; answered unsat: Z3 kept check assumptions at the base level and dropped them
; from unsat cores, so Sundance learned an invalid arithmetic lemma.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const p Bool)
(assert (or (not (< x y)) (= x y)))
(assert (or p (not (= y (+ x 2)))))
(check-sat)
