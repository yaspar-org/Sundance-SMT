(declare-fun % () Int)
(declare-fun h (Int) Bool)
(declare-const k Int)
(assert (h k))
(assert (= k %))
(assert (not (h (+ 0 %))))
(check-sat)


; strategy if in the arithmetic model (+ 0 %) = %
; add this clause: (+ 0 %) = % \/ (+ 0 %) > % \/ (+ 0 %) < %
; question: how do we figure out when do add this clause
; -> do it based on roots in the egraph
;     -> explicitly loop through the roots and add the equality "var_{term_id} = term"
;                                                                   var_100 = (+ 0 %) -> giving this to arithmetic solver



; example: 
; (h t) = (+ 1 0)
; (h t) = y [correspond to literal: -7]
; egraph: (h t) [1] -> y [2]
; give to albion: var_2 = (+ 1 0)

; map from terms -> albion variables: get it from a conversion context (datastructure: assignments)