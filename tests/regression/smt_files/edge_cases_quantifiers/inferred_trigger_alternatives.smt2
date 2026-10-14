; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; Both (P x) and (Q x) cover x. Only (Q c) occurs in the ground terms, so the
; instance x := c needs (Q x); z3 uses every such candidate as an alternative
; trigger.
(set-logic UFLIA)
(declare-sort T 0)
(declare-fun P (T) Bool)
(declare-fun Q (T) Bool)
(declare-const c T)
(assert (forall ((x T)) (and (P x) (Q x))))
(assert (not (Q c)))
(check-sat)
