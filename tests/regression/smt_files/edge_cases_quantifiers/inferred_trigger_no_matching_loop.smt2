; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; (f x), (g x) and (f (g x)) all cover x. (f x) is looping: matching it on f(a)
; creates f(g(a)), which matches again, forever. Like z3, inference drops it
; (and (f (g x)), which contains the candidate (g x)) and uses (g x). There is
; no g-term, so instantiation saturates.
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a Int)
(assert (forall ((x Int)) (= (f x) (f (g x)))))
(assert (= (f a) 0))
(check-sat)
