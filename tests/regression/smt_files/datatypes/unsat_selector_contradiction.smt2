; Test unsatisfiable selector contradictions
(declare-sort A 0)
(declare-sort B 0)
(declare-datatypes ((Pair 0)) (((mk-pair (fst A) (snd B)))))

(declare-const a1 A)
(declare-const a2 A)
(declare-const b1 B)
(declare-const p Pair)

; Create contradiction: selector values inconsistent with construction
(assert (= p (mk-pair a1 b1)))
(assert (= (fst p) a2))
(assert (not (= a1 a2)))

(check-sat)
