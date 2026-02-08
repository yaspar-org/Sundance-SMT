; Test constructor disjointness properties
(declare-sort X 0)
(declare-sort Y 0)
(declare-datatypes ((Shape 0)) (
  ((Circle (radius X))
   (Square (side X))
   (Rectangle (width X) (height Y))
   (Point))))

(declare-const x1 X)
(declare-const x2 X)  
(declare-const y1 Y)
(declare-const s1 Shape)
(declare-const s2 Shape)

; Test that different constructors create distinct values
(assert (not (= (Circle x1) (Square x1))))
(assert (not (= (Circle x1) (Rectangle x1 y1))))
(assert (not (= (Circle x1) Point)))
(assert (not (= (Square x1) (Rectangle x1 y1))))
(assert (not (= (Square x1) Point)))
(assert (not (= (Rectangle x1 y1) Point)))

; Test that constructors with same field values but different constructors are distinct
(assert (not (= (Circle x1) (Square x1))))
(assert (not (= (Rectangle x1 y1) (Rectangle x2 y1))))
(assert (= (Rectangle x1 y1) (Rectangle x1 y1)))

; Test recognizers enforce disjointness
(assert ((_ is Circle) (Circle x1)))
(assert (not ((_ is Square) (Circle x1))))
(assert (not ((_ is Rectangle) (Circle x1))))
(assert (not ((_ is Point) (Circle x1))))

(assert ((_ is Square) (Square x1)))
(assert (not ((_ is Circle) (Square x1))))
(assert (not ((_ is Rectangle) (Square x1))))
(assert (not ((_ is Point) (Square x1))))

(assert ((_ is Rectangle) (Rectangle x1 y1)))
(assert (not ((_ is Circle) (Rectangle x1 y1))))
(assert (not ((_ is Square) (Rectangle x1 y1))))
(assert (not ((_ is Point) (Rectangle x1 y1))))

(assert ((_ is Point) Point))
(assert (not ((_ is Circle) Point)))
(assert (not ((_ is Square) Point)))
(assert (not ((_ is Rectangle) Point)))

; Test mutual exclusion with variables
(assert ((_ is Circle) s1))
(assert (not (or ((_ is Square) s1) ((_ is Rectangle) s1) ((_ is Point) s1))))

; Test exhaustiveness
(assert (or ((_ is Circle) s2) ((_ is Square) s2) ((_ is Rectangle) s2) ((_ is Point) s2)))

; Test that exactly one recognizer is true
(assert (not (and ((_ is Circle) s2) ((_ is Square) s2))))
(assert (not (and ((_ is Circle) s2) ((_ is Rectangle) s2))))
(assert (not (and ((_ is Circle) s2) ((_ is Point) s2))))
(assert (not (and ((_ is Square) s2) ((_ is Rectangle) s2))))
(assert (not (and ((_ is Square) s2) ((_ is Point) s2))))
(assert (not (and ((_ is Rectangle) s2) ((_ is Point) s2))))

(check-sat)
