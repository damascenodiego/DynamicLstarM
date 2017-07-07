(define-sort Feature () Bool)
(declare-const G Feature)
(declare-const A Feature)
(declare-const M Feature)
(declare-const L Feature)
(declare-const C Feature)
(declare-const R Feature)
(declare-const B Feature)
(declare-const N Feature)
(declare-const W Feature)
(declare-const V Feature)
(declare-const Y Feature)
(declare-const P Feature)
(declare-const S Feature)

(assert G)
(assert (and
   (= A G)
   (= M A)
   (= L A)
   (= C G)
   (= R G)
   (= (or B  N  W ) R)
   (not (and B N))
   (not (and B W))
   (not (and N W))
   (= V G)
   (= Y V)
   (= P V)
   (=> S V)
))

(push)
(assert P)
(assert (and G W ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G N N N ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G N N S ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G W W S ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G W W W ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G B B B ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G W W S S B B B ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G B B S ))
(check-sat)
(pop)
(push)
(assert P)
(assert (and G W W S S B B S ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G W W S S N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G W P N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G W W S P N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G W W W P N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G B B B P N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G W W S S B B B P N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G B B S P N ))
(check-sat)
(pop)
(push)
(assert N)
(assert (and G W W S S B B S P N ))
(check-sat)
(pop)
(push)
(assert W)
(assert (and G W ))
(check-sat)
(pop)
(push)
(assert W)
(assert (and G W P W ))
(check-sat)
(pop)
(push)
(assert W)
(assert (and G N N N P W ))
(check-sat)
(pop)
(push)
(assert W)
(assert (and G N N S P W ))
(check-sat)
(pop)
(push)
(assert W)
(assert (and G B B B P W ))
(check-sat)
(pop)
(push)
(assert W)
(assert (and G B B S P W ))
(check-sat)
(pop)
(push)
(assert B)
(assert (and G B ))
(check-sat)
(pop)
(push)
(assert B)
(assert (and G W W S S B ))
(check-sat)
(pop)
(push)
(assert B)
(assert (and G W P B ))
(check-sat)
(pop)
(push)
(assert B)
(assert (and G N N N P B ))
(check-sat)
(pop)
(push)
(assert B)
(assert (and G N N S P B ))
(check-sat)
(pop)
(push)
(assert B)
(assert (and G W W S P B ))
(check-sat)
(pop)
(push)
(assert B)
(assert (and G W W W P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G W W S ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G W P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G N N N P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G N N S P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G W W S P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G W W W P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G B B B P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G B B S P B ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G W P N ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G N N N P N ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G N N S P N ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G W W S P N ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G W W W P N ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G B B B P N ))
(check-sat)
(pop)
(push)
(assert S)
(assert (and G B B S P N ))
(check-sat)
(pop)
