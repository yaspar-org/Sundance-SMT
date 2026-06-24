; Multiple recursive constructors, all paths lead to a cycle.
; x is ctorA_r1, its B-child cannot be safe, and regardless of which B-constructor
; is chosen (ctorB_r1 or ctorB_r2), the resulting A-grandchild equals x.
(set-logic ALL)
(declare-datatypes ((A 0) (B 0) (D 0))
  (((ctorA_r1 (selAr1 B)) (ctorA_r2 (selAr2 B)) (ctorA_safe (selAs D)))
   ((ctorB_r1 (selBr1 A)) (ctorB_r2 (selBr2 A)) (ctorB_safe (selBs D)))
   ((ctorD_val (selD Int)))))
(declare-const x A)
(assert ((_ is ctorA_r1) x))
(assert (not ((_ is ctorB_safe) (selAr1 x))))
(assert (=> ((_ is ctorB_r1) (selAr1 x)) (= (selBr1 (selAr1 x)) x)))
(assert (=> ((_ is ctorB_r2) (selAr1 x)) (= (selBr2 (selAr1 x)) x)))
(check-sat)
