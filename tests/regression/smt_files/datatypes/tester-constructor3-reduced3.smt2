; Further reduction that exposes: the recursive Boolean-subterm
; classification must run for ALL Atom fallbacks in classify_recursive,
; not just the App/catch-all branch.
;
; Here (= P (B (or (= s (% P))))) is a non-Bool Eq (P-typed sides), so
; classify_recursive's Eq branch falls through to Atom because the sides
; lack SAT lits. Without recursing from that Atom fallback, the inner
; (or (= s (% P))) never gets an Or NodeKind, and (= s (% P)) never
; becomes relevant.
(declare-sort P 0)
(declare-fun B (Bool) P)
(assert (forall ((x Bool)) (! x :pattern ((B x)))))
(declare-datatypes ((s 0)) (((s) (se))))
(declare-fun P () P)
(declare-fun % (P) s)
(assert (= se (% P)))
(assert (= P (B (or (= s (% P))))))
(check-sat)
