(define-sort Feature () Bool)
(declare-const f0 Feature)
(declare-const f1 Feature)
(declare-const f2 Feature)
(declare-const f3 Feature)
(declare-const f4 Feature)
(declare-const f5 Feature)
(declare-const f6 Feature)
(declare-const f7 Feature)
(declare-const f8 Feature)
(declare-const f9 Feature)
(declare-const f10 Feature)
(declare-const f11 Feature)
(declare-const f12 Feature)
(declare-const f13 Feature)
(declare-const f14 Feature)
(declare-const f15 Feature)
(declare-const f16 Feature)
(declare-const f17 Feature)
(declare-const f18 Feature)
(declare-const f19 Feature)
(declare-const f20 Feature)

(assert f0)
(assert (and
   (=> f1 f0)
   (=> f2 f1)
   (=> f3 f2)
   (=> f4 f3)
   (=> f5 f4)
   (=> f6 f5)
   (=> f7 f6)
   (=> f8 f7)
   (=> f9 f8)
   (=> f10 f9)
   (=> f11 f10)
   (=> f12 f11)
   (=> f13 f12)
   (=> f14 f13)
   (=> f15 f14)
   (=> f16 f15)
   (=> f17 f16)
   (=> f18 f17)
   (=> f19 f18)
   (=> f20 f19)
))

(push)
(assert (and f19 f20))
(assert (and f19 f18 f20 f19))
(check-sat)
(pop)
(push)
(assert (and f19 f20))
(assert (and f19 f19 f20 f20))
(check-sat)
(pop)
