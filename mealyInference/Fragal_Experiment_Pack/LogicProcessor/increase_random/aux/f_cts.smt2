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

(push)
(assert (and f0 f0 f0))
(check-sat)
(pop)
(push)
(assert (and f0 f6 f6))
(check-sat)
(pop)
(push)
(assert (and f6 f6 f0))
(check-sat)
(pop)
(push)
(assert (and f6 f6 f6))
(check-sat)
(pop)
(push)
(assert (and f6 f3 f3))
(check-sat)
(pop)
(push)
(assert (and f3 f3 f6))
(check-sat)
(pop)
(push)
(assert (and f3 f3 f3))
(check-sat)
(pop)
(push)
(assert (and f3 f2 f2))
(check-sat)
(pop)
(push)
(assert (and f2 f2 f3))
(check-sat)
(pop)
(push)
(assert (and f2 f2 f2))
(check-sat)
(pop)
(push)
(assert (and f6 f4 f4))
(check-sat)
(pop)
(push)
(assert (and f4 f4 f6))
(check-sat)
(pop)
(push)
(assert (and f4 f4 f4))
(check-sat)
(pop)
(push)
(assert (and f4 f1 f1))
(check-sat)
(pop)
(push)
(assert (and f1 f1 f4))
(check-sat)
(pop)
(push)
(assert (and f1 f1 f1))
(check-sat)
(pop)
(push)
(assert (and f6 f5 f5))
(check-sat)
(pop)
(push)
(assert (and f5 f5 f6))
(check-sat)
(pop)
(push)
(assert (and f5 f5 f5))
(check-sat)
(pop)
(push)
(assert (and f0 f7 f7))
(check-sat)
(pop)
(push)
(assert (and f7 f7 f0))
(check-sat)
(pop)
(push)
(assert (and f7 f7 f7))
(check-sat)
(pop)