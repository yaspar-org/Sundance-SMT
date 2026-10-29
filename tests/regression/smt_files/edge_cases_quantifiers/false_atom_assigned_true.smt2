; sat (z3 5.3.0: sat). The instance (or (not (= y (f 0))) (and true (or false (Q 0)))) is created at
; decision level 2 with (= y (f 0)) true and (Q 0) false, so BCP sets the `false` atom true. The
; semper e-graph (#224) explained that true=false collision with the empty clause and answered unsat.
; Expected: unknown (quantified sat).
(set-logic ALL)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun f (Int) Int)
(declare-const y Int)
(declare-const c Bool)
(assert (forall ((x Int)) (! (or (not (= y (f x))) (and true (or false (Q x)))) :pattern ((P (f x))))))
(assert (or (= y (f 0)) c))
(assert (P y))
(assert (not (Q 0)))
(check-sat)
