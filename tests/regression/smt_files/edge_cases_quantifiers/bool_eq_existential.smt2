; Existential appears as a direct operand of a Boolean equality
; `(= p (exists ...))`. Asserting `p` forces the existential true; the
; universal `(forall y. not (P y))` then contradicts it under
; e-matching. Regresses the CNF-side candidate registration plus the
; propagator's `cb_decide` wiring.
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-const p Bool)
(assert (= p (exists ((x U)) (! (P x) :pattern ((P x))))))
(assert p)
(assert (forall ((y U)) (! (not (P y)) :pattern ((P y)))))
(check-sat)
