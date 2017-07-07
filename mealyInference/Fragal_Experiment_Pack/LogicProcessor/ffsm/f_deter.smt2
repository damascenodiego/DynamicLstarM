(define-sort Feature () Bool)
(declare-const f1 Feature)
(declare-const f2 Feature)
(declare-const f3 Feature)

; assert feature root as true 
(assert f1)
(assert (and
   (= (or f2 f3) f1)
   (not (and f2 f3))
))

(assert (not (and 
    (and f1 f2 f2)
    (and f1 f3 (and f3 (not f2)))
)))
(check-sat)