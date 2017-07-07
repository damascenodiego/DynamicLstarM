(define-sort Feature () Bool)
(declare-const g Feature)
(declare-const a Feature)
(declare-const m Feature)
(declare-const l Feature)
(declare-const c Feature)
(declare-const r Feature)
(declare-const b Feature)
(declare-const n Feature)
(declare-const w Feature)
(declare-const v Feature)
(declare-const y Feature)
(declare-const p Feature)
(declare-const s Feature)

(assert g)
(assert (and
   (= a g)
   (= m a)
   (= l a)
   (= c g)
   (= r g)
   (= (or b n w) r)
   (not (and b n))
   (not (and b w))
   (not (and n w))
   (= v g)
   (= y v)
   (= p v)
   (=> s v)
))

(assert s)
(assert (and 
    (not (and w s))
    (not (and (not w) s))
))
(check-sat)