; Relevancy filtering restricts e-matching to terms whose SAT lits are
; marked relevant. When the outer OR `(or (= x y) (= x z))` fires the
; Or-TRUE rule, only ONE disjunct's equality flows into the egraph, so
; at most one of x=y / x=z is merged. The pattern `(g v v v)` needs
; g(t,t,t) — i.e. x, y, z all in one class — which requires BOTH
; merges. So the forall never instantiates, `¬h(x)` is never derived,
; and the contradiction with `(h x)` is missed. Expected: `unknown`.
; z3 with tuned flags (mbqi=false, eager_threshold=100) also returns
; unknown here — this is the correct behavior for pure e-matching, not
; a completeness gap in our implementation.
(set-logic ALL)
(declare-sort U 0)
(declare-fun g (U U U) Bool)
(declare-fun h (U) Bool)
(declare-const x U)
(declare-const y U)
(declare-const z U)
(assert (forall ((v U)) (! (not (h v)) :pattern ((g v v v)))))
(assert (or (= x y) (= x z)))
(assert (g x y z))
(assert (h x))
(check-sat)
