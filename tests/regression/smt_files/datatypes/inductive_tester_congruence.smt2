; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; Issue #260: the tester (_ is B) t created at the final model check must be
; merged by congruence with the asserted (_ is B) u once t = u.
(set-logic ALL)
(declare-datatype T ((A) (B) (C (c T))))
(declare-const t T)
(declare-const u T)
(assert (= t u))
(assert ((_ is A) t))
(assert ((_ is B) u))
(check-sat)
