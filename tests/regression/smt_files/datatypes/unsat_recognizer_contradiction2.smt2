; Test unsatisfiable recognizer contradictions
(declare-sort A 0)
(declare-sort B 0)
(declare-datatypes ((Data 0)) (((Variant1 (field1 A)) (Variant2 (field2 B)))))

(declare-const x Data)
(declare-const y Data)
(declare-const a A)
(declare-const b B)

; Create contradiction: x cannot be both variants
(assert ((_ is Variant1) x))
(assert ((_ is Variant2) y))
(assert (= x y))

(check-sat)
