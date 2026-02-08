; Basic record datatype test
(declare-sort Name 0)
(declare-sort Age 0)
(declare-datatypes ((Person 0)) (((mk-person (name Name) (age Age)))))

(declare-const john Name)
(declare-const mary Name)
(declare-const age1 Age)
(declare-const age2 Age)
(declare-const p1 Person)
(declare-const p2 Person)

; Test constructor and recognizers
(assert ((_ is mk-person) (mk-person john age1)))
(assert ((_ is mk-person) p1))

; Test selectors
(assert (= (name (mk-person john age1)) john))
(assert (= (age (mk-person john age1)) age1))

; Test constructor injectivity
(assert (not (= (mk-person john age1) (mk-person mary age1))))
(assert (not (= (mk-person john age1) (mk-person john age2))))

; Test selector-constructor relationship
(assert (= p1 (mk-person (name p1) (age p1))))

; Test equality between constructed values
(assert (= (mk-person john age1) (mk-person john age1)))

(check-sat)
