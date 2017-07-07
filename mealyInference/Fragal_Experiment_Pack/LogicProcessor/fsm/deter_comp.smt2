(define-sort State () Int)
(define-sort Input () Int)
(define-sort Output () Int)

(declare-fun NextState (State Input) State)
(declare-fun Domain (State Input) State)
(declare-fun Transition (State Input Output State) Bool)

; initialize transitions
(assert (forall ((x State) (i Input) (o Output) (y State)) (
  => (Transition x i o y)
   (and (= y (NextState x i)) (= i (Domain x i)) ))))

; deterministic property
(assert (forall ((x State) (i Input) (y State) (z State)
    (o1 Output) (o2 Output)) (
  => (and (= y (NextState x i)) (= z (NextState x i))
          (Transition x i o1 y) (Transition x i o2 z))
     (and (= y z) (= o1 o2))
  ))) 

; the mapping is handled by java implementation
(assert (Transition 1 1 1 1))
(assert (Transition 1 2 2 2))
(assert (Transition 2 1 2 1))
(assert (Transition 3 1 1 3))
(check-sat)
(eval (and 
  (=  1 (Domain 1 1))
  (=  2 (Domain 1 2))
  (=  1 (Domain 2 1))
  (=  2 (Domain 2 2))
  (=  1 (Domain 3 1))
  (=  2 (Domain 3 2))
))
