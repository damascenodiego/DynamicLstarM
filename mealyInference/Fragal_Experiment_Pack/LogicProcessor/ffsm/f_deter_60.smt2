(define-sort Feature () Bool)
(declare-const f1 Feature)
(declare-const f11 Feature)
(declare-const f2 Feature)
(declare-const f3 Feature)
(declare-const f4 Feature)
(declare-const f5 Feature)
(declare-const f6 Feature)
(declare-const f7 Feature)
(declare-const f8 Feature)
(declare-const f9 Feature)
(declare-const f20 Feature)
(declare-const f21 Feature)
(declare-const f22 Feature)
(declare-const f23 Feature)
(declare-const f24 Feature)

(assert f1)
(assert (and
   (= f11 f1)
   (= (or f2 f3 f4) f11)
   (not (and f2 f3))
   (not (and f2 f4))
   (not (and f3 f4))
   (=> f5 f1)
   (=> f6 f1)
   (=> f7 f1)
   (=> f8 f1)
   (=> f9 f1)
   (=> f20 f1)
   (=> f21 f1)
   (=> f22 f1)
   (=> f23 f1)
   (=> f24 f1)
))

(assert (and 
    (and f1 f20 f20)
    (and f1 f24 f24)
))
(check-sat)