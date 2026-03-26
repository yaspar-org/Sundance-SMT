; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; define-fun used multiple times with different arguments (sat case)
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun a () T)
(declare-fun b () T)
(declare-fun c () T)
(declare-fun f (T) T)
(define-fun g ((x T)) T (f x))
(assert (= (g a) b))
(assert (= (g b) c))
(assert (not (= a c)))
(check-sat)
