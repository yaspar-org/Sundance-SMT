; Direct self-cycle: x = Cons(1, x) is not well-founded
(set-logic ALL)
(declare-datatypes ((List 1)) ((par (T) ((Nil) (Cons (head T) (tail (List T)))))))
(declare-const x (List Int))
(assert (= x (Cons 1 x)))
(check-sat)
