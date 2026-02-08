(declare-const x Bool)
(declare-sort F 0)
(declare-fun u (F) F)
(declare-sort P 0)
(declare-sort T 0)
(declare-sort D 0)
(declare-const $ D)
(declare-fun S (Int Int) Int)
(declare-sort vs 0)
(declare-sort lib 0)
(declare-sort lib!s 0)
(declare-fun is-lib!be (lib) Bool)
(declare-fun b (lib) vs)
(declare-const T T)
(declare-fun P (vs) P)
(declare-fun o (lib) P)
(declare-fun % (P) lib)
(declare-fun Po (lib!s) P)
(declare-fun vs (D T P) Int)
(declare-fun v (P P) P)
(declare-fun ib (P P) Bool)
(declare-fun l (P) Bool)
(declare-fun i (P F) Bool)
(declare-fun li (P) vs)
(declare-fun lib (P P) Int)
(declare-fun b! (P P F) Int)
(declare-fun ib! (P P) Int)
(declare-const p0 P)
(declare-const p1 P)
(assert (forall ((a P) (b P)) (! (= (ib a b) (not (= a b))) :pattern ((ib a b)))))
(assert (forall ((r P)) (! (= (l r) (forall ((j P)) (! (ib (v r j) (v r j)) :pattern ((v r j))))) :pattern ((l r)))))
(assert (forall ((e P) (ue F)) (! (= (i e (u ue)) (l (P (b (% e))))) :pattern ())))
(declare-const f F)
(assert (forall ((r P) (e P) (ue F)) (! (= (b! r r (u ue)) (ite (ib e (v r p0)) (S 0 1) (b! p1 r ue))) :pattern ((b! r e (u ue))))))

;(assert (forall ((r P) (e P)) (! (= (lib r r) (b! r e (u f))) :pattern ((lib r e)))))



;(assert (forall ((e P) (k P)) (! (= (lib e e) (lib k (P (ite (is-lib!be (% k)) (b (% k)) (b (% k)))))) :pattern ((ib! e k)))))



;(assert (forall ((e P) (k P)) (! (or x (and (= (P (li k)) k) (forall ((i P)) (! (or x (ib k (P (li i)))) :pattern ((li i)))))) :pattern ((ib! e k)))))


(declare-const n lib)
(declare-const k lib!s)
(declare-const s vs)
(assert (and (not (ib (Po k) (P s))) (= (ib! (o n) (Po k)) (vs $ T (P (li (o n)))))))
(assert (or x (and (= (P (li (Po k))) (Po k)) (forall ((i P)) (! (or x (ib (Po k) (P (li i)))) :pattern ((li i)))))))
(assert (= (lib (Po k) (Po k)) (b! (Po k) (P (ite (is-lib!be (% (Po k))) (b (% (Po k))) (b (% (Po k))))) (u f))))

;(assert (or x (ib (Po k) (P (li (Po k))))))


