(define-sort Feature () Bool)
(declare-const f0 Feature)
(declare-const f6 Feature)
(declare-const f3 Feature)
(declare-const f2 Feature)
(declare-const f4 Feature)
(declare-const f1 Feature)
(declare-const f5 Feature)
(declare-const f7 Feature)

(assert f0)
(assert (and
   (=> f6 f0)
   (=> f2 f3)
   (=> f1 f4)
   (= (or f3  f4  f5 ) f6)
   (=> f7 f0)
))

(assert (and f5 f7))
(assert (and 
    (not (and f5 f5 f7 f7 ))
))
(check-sat)