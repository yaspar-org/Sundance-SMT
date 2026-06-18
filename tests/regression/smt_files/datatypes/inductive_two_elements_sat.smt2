; Two distinct list elements, no cycle
(set-logic ALL)
(declare-datatypes ((List 1)) ((par (T) ((Nil) (Cons (head T) (tail (List T)))))))
(declare-const x (List Int))
(declare-const y (List Int))
(assert (= x (Cons 1 y)))
(assert (= y (Cons 2 (as Nil (List Int)))))
(assert (not (= x y)))
(check-sat)
