; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; Dafny-style constructor test: is_C(x) <=> exists a. x = C(a). is_C(C 5) is
; false, so the exists is false and acts as a forall. It has no :pattern, so it
; needs an inferred trigger, (C a), to produce the instance a := 5.
(set-logic UFLIA)
(declare-sort T 0)
(declare-fun C (Int) T)
(declare-fun is_C (T) Bool)
(assert (forall ((x T)) (! (= (is_C x) (exists ((a Int)) (= x (C a)))) :pattern ((is_C x)))))
(assert (not (is_C (C 5))))
(check-sat)
