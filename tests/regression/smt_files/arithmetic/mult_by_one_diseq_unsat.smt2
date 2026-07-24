; Regression: a disequality between arithmetic terms with no explicit
; inequality/equality constraints must still be refuted. `(* 1 y)` linearizes
; to `y`, so `(not (= (* 1 y) y))` is unsat. Previously the eager `internal`
; and `z3` backends short-circuited to `sat` because extract_linear_constraints
; produced no constraints, skipping the definitional equalities needed for
; Nelson-Oppen. See lialp.rs / z3lp.rs early-return guard.
(set-logic ALL)
(declare-const y Int)
(assert (not (= (* 1 y) y)))
(check-sat)
