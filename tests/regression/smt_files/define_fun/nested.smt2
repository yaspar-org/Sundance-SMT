; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; nested define-fun: one defined function calls another
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun a () T)
(declare-fun b () T)
(declare-fun f (T) T)
(define-fun g ((x T)) T (f x))
(define-fun gg ((x T)) T (g (g x)))
(assert (= (gg a) b))
(assert (not (= (f (f a)) b)))
(check-sat)
