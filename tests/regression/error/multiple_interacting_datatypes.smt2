; Test multiple interacting datatypes
(declare-datatypes ((Color 0) (Material 0) (Object 0)) (
  ((Red) (Blue) (Green))
  ((Wood) (Metal) (Plastic))
  ((Ball (ball-color Color) (ball-material Material))
   (Box (box-color Color) (box-material Material) (contents Object)))))

(declare-const c1 Color)
(declare-const c2 Color)
(declare-const m1 Material)
(declare-const m2 Material)
(declare-const obj1 Object)
(declare-const obj2 Object)
(declare-const ball1 Object)
(declare-const box1 Object)

; Test basic datatype interactions
(assert (= ball1 (Ball Red Wood)))
(assert (= box1 (Box Blue Metal ball1)))

; Test nested structure - box containing a ball
(assert ((_ is Ball) (contents box1)))
(assert (= (contents box1) ball1))
(assert (= (ball-color (contents box1)) Red))
(assert (= (ball-material (contents box1)) Wood))

; Test constructor combinations across datatypes
(assert (not (= (Ball Red Wood) (Ball Blue Wood))))
(assert (not (= (Ball Red Wood) (Ball Red Metal))))
(assert (not (= (Box Red Wood obj1) (Ball Red Wood))))

; Test selectors work correctly across types
(assert (= (box-color box1) Blue))
(assert (= (box-material box1) Metal))
(assert (= (ball-color ball1) Red))
(assert (= (ball-material ball1) Wood))

; Test recognizers work across datatypes
(assert ((_ is Ball) ball1))
(assert ((_ is Box) box1))
(assert (not ((_ is Ball) box1)))
(assert (not ((_ is Box) ball1)))

; Test complex nested equality
(assert (= (Box Blue Metal (Ball Red Wood)) box1))
(assert (not (= (Box Blue Metal (Ball Green Wood)) box1)))

; Test with variables constrained to be different datatypes
(assert ((_ is Ball) obj1))
(assert ((_ is Box) obj2))
(assert (not (= obj1 obj2)))

; Test selector-constructor round trips with nested types
(assert (= box1 (Box (box-color box1) (box-material box1) (contents box1))))
(assert (= ball1 (Ball (ball-color ball1) (ball-material ball1))))

; Test that different enum values create different objects
(assert (not (= (Ball Red Wood) (Ball Green Wood))))
(assert (not (= (Ball Red Wood) (Ball Red Plastic))))

(check-sat)
