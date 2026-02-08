; Test constructor injectivity properties
(declare-sort A 0)
(declare-sort B 0)
(declare-sort C 0)
(declare-datatypes ((Triple 0)) (((mk-triple (first A) (second B) (third C)))))

(declare-const a1 A)
(declare-const a2 A)
(declare-const b1 B)
(declare-const b2 B)
(declare-const c1 C)
(declare-const c2 C)
(declare-const t1 Triple)
(declare-const t2 Triple)

; Test basic constructor injectivity - if constructed values are equal, fields must be equal
(assert (= (mk-triple a1 b1 c1) (mk-triple a2 b2 c2)))
(assert (= a1 a2))
(assert (= b1 b2))
(assert (= c1 c2))

; Test constructor injectivity contrapositive - if fields differ, constructed values differ
(assert (not (= a1 a2)))
(assert (not (= (mk-triple a1 b1 c1) (mk-triple a2 b1 c1))))

(assert (not (= b1 b2)))
(assert (not (= (mk-triple a1 b1 c1) (mk-triple a1 b2 c1))))

(assert (not (= c1 c2)))
(assert (not (= (mk-triple a1 b1 c1) (mk-triple a1 b1 c2))))

; Test selector extraction preserves equality
(assert (= t1 t2))
(assert (= (first t1) (first t2)))
(assert (= (second t1) (second t2)))
(assert (= (third t1) (third t2)))

; Test constructor-selector round trip
(assert (= t1 (mk-triple (first t1) (second t1) (third t1))))

; Test that different field values create different triples
(assert (not (= (mk-triple a1 b1 c1) (mk-triple a2 b1 c1))))
(assert (not (= (mk-triple a1 b1 c1) (mk-triple a1 b2 c1))))
(assert (not (= (mk-triple a1 b1 c1) (mk-triple a1 b1 c2))))

(check-sat)
