(set-logic ALL)
(declare-datatypes ((Tree 0)) (((Leaf (val Int)) (Node (left Tree) (right Tree)))))
(declare-const t Tree)
; t is a Node whose left child is itself — cycle
(assert ((_ is Node) t))
(assert (= (left t) t))
(check-sat)
