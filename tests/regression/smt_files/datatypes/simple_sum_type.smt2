; Simple sum type - variants without fields
(declare-datatypes ((Color 0)) (((Red) (Green) (Blue))))

(declare-const c1 Color)
(declare-const c2 Color)

; Test constructor recognizers
(assert ((_ is Red) Red))
(assert ((_ is Green) Green))
(assert ((_ is Blue) Blue))

; Test constructor distinctness
(assert (not (= Red Green)))
(assert (not (= Red Blue)))
(assert (not (= Green Blue)))

; Test with variables
(assert ((_ is Red) c1))
(assert (not ((_ is Green) c1)))
(assert (not ((_ is Blue) c1)))

; Test exhaustiveness
(assert (or ((_ is Red) c2) ((_ is Green) c2) ((_ is Blue) c2)))

; Test mutual exclusion
(assert (not (and ((_ is Red) c2) ((_ is Green) c2))))
(assert (not (and ((_ is Red) c2) ((_ is Blue) c2))))
(assert (not (and ((_ is Green) c2) ((_ is Blue) c2))))

(check-sat)
