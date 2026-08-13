; Tree forced to be a Node ((left t) = t plus (is-Node t)) is a self-subterm
; cycle. Unsat via occurs check even though the tester is asserted separately
; from the equality.
(set-logic ALL)
(declare-datatypes ((Tree 0))
  (((Leaf (val Int)) (Node (left Tree) (right Tree)))))
(declare-const t Tree)
(assert ((_ is Node) t))
(assert (= (left t) t))
(check-sat)
