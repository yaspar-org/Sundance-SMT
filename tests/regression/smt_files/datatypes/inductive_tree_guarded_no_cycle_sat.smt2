; Binary tree: (left t) = t is only a cycle if t is a Node. Leaf is a base case,
; so t = Leaf satisfies the equality (left t is unconstrained). The occurs-check
; conflict must be guarded by (not (is-Node t)).
(set-logic ALL)
(declare-datatypes ((Tree 0))
  (((Leaf (val Int)) (Node (left Tree) (right Tree)))))
(declare-const t Tree)
(assert (= (left t) t))
(check-sat)
