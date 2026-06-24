; Cycle through selector: tail(x) = x
(set-logic ALL)
(declare-datatypes ((List 1)) ((par (T) ((Nil) (Cons (head T) (tail (List T)))))))
(declare-const x (List Int))
(assert ((_ is Cons) x))
(assert (= (tail x) x))
(check-sat)
