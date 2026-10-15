; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

(set-logic QF_UFLIA)
; (+ 0 x) = x, so congruence gives (g x) = (g (+ 0 x)). The E-graph keeps x and
; (+ 0 x) apart; only the arithmetic model makes them equal. The Nelson-Oppen probe
; merge of x and (+ 0 x) used to be accepted because it raised no E-graph conflict,
; although the equality it implies, (g x) = (g (+ 0 x)), contradicts the model.
; Random fuzz case (seed 2635), ddsmt-reduced.
(declare-fun g (Int) Int)
(declare-const x Int)
(assert (> (g x) (g (+ 0 x))))
(check-sat)
