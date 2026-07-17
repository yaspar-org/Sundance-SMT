(set-logic AUFLIA)
(declare-const a Int)
(declare-const b Int)
(declare-fun p (Int) Bool)
(declare-fun f (Int) Int)

(assert
  (forall ((x Int))
    (! (= (f x) 0)
       :pattern ((p x)))))

; Register the farther trigger first.
(assert (p b))
(assert (p a))

; The nearest instance is propositionally consistent but arithmetically false.
(assert (> (f a) 0))
(check-sat)
