; Without the exclusion, the shallower/lexically-first (a x) would be selected,
; but no ground (a A) exists. Excluding it forces (z x), which fires on (z A).
(set-logic ALL)
(declare-sort U 0)
(declare-const A U)
(declare-const B U)
(declare-fun a (U) Bool)
(declare-fun z (U) Bool)
(assert (forall ((x U)) (! (=> (z x) (or (= x B) (and false (a x)))) :no-pattern (a x))))
(assert (z A))
(assert (distinct A B))
(check-sat)
