; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; define-fun with arithmetic
(set-logic LIA)
(define-fun add_one ((x Int)) Int (+ x 1))
(declare-fun n () Int)
(assert (= (add_one n) 5))
(assert (not (= n 4)))
(check-sat)
