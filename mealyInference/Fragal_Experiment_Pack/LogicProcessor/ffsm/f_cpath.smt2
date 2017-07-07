(define-sort Feature () Bool)
(declare-const f1 Feature)
(declare-const f11 Feature)
(declare-const f2 Feature)
(declare-const f3 Feature)
(declare-const f4 Feature)
(declare-const f5 Feature)

(assert f1)
(assert (and
   (= f11 f1)
   (= (or f2 f3 f4) f11)
   (not (and f2 f3))
   (not (and f2 f4))
   (not (and f3 f4))
   (=> f5 f1)
))

(assert f2)
(assert (and 
    (not (and f1 f2 f2 f2 ))
))
(check-sat)