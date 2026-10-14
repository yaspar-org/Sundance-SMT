; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

(set-logic QF_UFLIA)
; Satisfiable counterpart: x and (+ 1 x) always differ, so (g x) > (g (+ 1 x)) is fine.
(declare-fun g (Int) Int)
(declare-const x Int)
(assert (> (g x) (g (+ 1 x))))
(check-sat)
