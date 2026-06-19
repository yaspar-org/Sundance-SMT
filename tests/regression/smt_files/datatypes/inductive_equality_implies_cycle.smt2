(set-logic ALL)
(declare-datatypes ((List 1)) ((par (T) ((Nil) (Cons (head T) (tail (List T)))))))
(declare-const x (List Int))
(declare-const y (List Int))
; x = Cons(1, y), y = x — implies x = Cons(1, x), which is a cycle
(assert (= x (Cons 1 y)))
(assert (= y x))
(check-sat)
