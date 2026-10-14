; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

(set-logic ALL)
; An E-graph equality between Int terms never reached the arithmetic solver. The
; "arithmetic" flag lived on the class root's proof-forest edge; terms created by
; instances were congruence-merged into an arithmetic class at birth, and when
; backtracking split them out again the restored root edge (saved at union time)
; carried no flag. The replayed congruence merge of two such classes, here
; (len d ty m) ~ (len d ty (boxSeq ..)), was then never queued for the solver, so it
; gave them different values and the saturated model was accepted (unknown).
; ddsmt-reduced from Verus splinterdb/betree__PivotBetree_v.4.smt2.
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun unI (Poly) Int)
(declare-sort Ty 0)
(declare-sort Dcr 0)
(declare-const d Dcr)
(assert (forall ((x Int)) (! (= x (unI (I 0))) :pattern ((I x)))))
(declare-fun Sub (Int Int) Int)
(assert (forall ((x Int) (y Int)) (! (= (- x) (Sub 1 0)) :pattern ((Sub x y)))))
(declare-sort Sq 0)
(declare-datatypes ((Node 0) (PTable 0)) (((node)) ((ptable))))
(declare-fun pivots (Node) PTable)
(declare-fun seqof (PTable) Sq)
(declare-const ty Ty)
(declare-fun boxSeq (Sq) Poly)
(declare-fun unboxNode (Poly) Node)
(declare-fun boxTable (PTable) Poly)
(declare-fun unboxTable (Poly) PTable)
(declare-fun len (Dcr Ty Poly) Int)
(declare-fun num_ranges (Poly) Int)
(declare-fun index_ok (Dcr Ty Poly Poly) Bool)
(assert (forall ((dd Dcr) (tt Ty) (s Poly) (ii Poly)) (! (= (index_ok dd ty s ii) (< (unI ii) (len dd ty s))) :pattern ((index_ok dd tt s ii)))))
(declare-fun req (Poly) Bool)
(assert (forall ((b Poly)) (! (= true (req b)) :pattern ((req b)))))
(declare-fun last_req (Dcr Ty Poly) Bool)
(assert (forall ((dd Dcr) (tt Ty) (s Poly)) (! (= 0 (len dd ty s)) :pattern ((last_req dd tt s)))))
(assert (or (forall ((s Poly)) (! (= (num_ranges s) (Sub (len d ty (boxSeq (seqof (unboxTable s)))) 1)) :pattern ((num_ranges s))))))
(declare-const self Poly)
(declare-const m Poly)
(assert (or (not (req self)) (and (= (boxSeq (seqof (unboxTable (boxTable (pivots (unboxNode self)))))) (B (= 0 (num_ranges (boxTable (pivots (unboxNode self))))))) (or (not (index_ok d ty (B (= 0 (num_ranges (boxTable (pivots (unboxNode self)))))) (I 0))) (not (=> false (last_req d ty m) (= m (boxSeq (seqof (unboxTable (boxTable (pivots (unboxNode self)))))))))))))
(check-sat)
