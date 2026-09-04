; Further reduction that exposes the App-args Boolean-subterm
; classification bug. With (assert (B true)) alongside
; (assert (B (or (= s (P se))))), QI only instantiates the trivial
; x=true (never x=(or (= s (P se)))). So the previous fix (register_node
; re-queue) doesn't help — the Or(1) NodeKind is never registered via QI.
;
; Fix: classify_recursive on an App (its catch-all fallback) now
; recursively classifies Boolean-connective sub-terms so their
; structural NodeKinds are registered UP FRONT at level 0.
(declare-const x Bool)
(declare-datatypes ((s 0)) (((s) (se))))
(declare-fun B (Bool) Bool)
(assert (forall ((x Bool)) (! x :pattern ((B x)))))
(declare-fun P (s) s)
(assert (B true))
(assert (= se (P se)))
(assert (B (or (= s (P se)))))
(check-sat)
