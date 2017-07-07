(define-sort State () Int)
(define-sort Input () Int)
(define-sort Output () Int)

(declare-fun NextState (State Input) State)
(declare-fun Path (State State) State)
(declare-fun Transition (State Input Output State) Bool)
(declare-var initialState State)

; initialize transitions
(assert (forall ((x State) (i Input) (o Output) (y State)) (
  => (and (Transition x i o y) (not (= x y)) )
    (and (= y (NextState x i)) (= y (Path x y)) ))))

; find all paths
(assert (forall ((s1 State) (s2 State) (s3 State))
   (=> (and (= s2 (Path s1 s2)) (= s3 (Path s2 s3))) 
    (= s3 (Path s1 s3)) ))) 

; the mapping is handled by java implementation
(assert (= initialState 1))
(assert (Transition 1 1 1 1))
(assert (Transition 1 2 2 2))
(assert (Transition 2 1 2 1))
(assert (Transition 3 1 1 3))
(check-sat)
(eval (and 
  (=  2 (Path initialState 2))
  (=  3 (Path initialState 3))
))
