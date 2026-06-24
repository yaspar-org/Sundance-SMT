; Non-cyclic: x = Cons(1, Nil) is well-founded
(set-logic ALL)
(declare-datatypes ((List 1)) ((par (T) ((Nil) (Cons (head T) (tail (List T)))))))
(declare-const x (List Int))
(assert (= x (Cons 1 (as Nil (List Int)))))
(check-sat)
