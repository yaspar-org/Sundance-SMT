; Cycle through conditional implication: x is ctorA_r1, its B-child must be
; ctorB_r1 (safe blocked), and the resulting A-grandchild equals x.
; The cycle x -> selAr1(x) -> selBr1(selAr1(x)) = x is forced by implications.
(set-logic ALL)
(declare-datatypes ((A 0) (B 0) (D 0))
  (((ctorA_r1 (selAr1 B)) (ctorA_safe (selAs D)))
   ((ctorB_r1 (selBr1 A)) (ctorB_safe (selBs D)))
   ((ctorD_val (selD Int)))))
(declare-const x A)
(assert ((_ is ctorA_r1) x))
(assert (not ((_ is ctorB_safe) (selAr1 x))))
(assert (=> ((_ is ctorB_r1) (selAr1 x)) (= (selBr1 (selAr1 x)) x)))
(check-sat)
