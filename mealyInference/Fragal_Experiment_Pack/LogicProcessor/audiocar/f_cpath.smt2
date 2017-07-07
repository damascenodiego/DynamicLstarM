(define-sort Feature () Bool)
(declare-const RAD Feature)
(declare-const WCON Feature)
(declare-const TRAF Feature)
(declare-const NAV Feature)
(declare-const MAPUSB Feature)
(declare-const MAPCD Feature)
(declare-const P Feature)
(declare-const USB Feature)
(declare-const O Feature)
(declare-const CD Feature)
(declare-const CASS Feature)
(declare-const C Feature)
(declare-const CHAN Feature)
(declare-const FWBW Feature)
(declare-const V Feature)
(declare-const S Feature)

(assert RAD)
(assert (and
   (=> WCON RAD)
   (= TRAF RAD)
   (=> NAV RAD)
   (=> MAPUSB NAV)
   (=> MAPCD NAV)
   (= P RAD)
   (=> USB P)
   (= O P)
   (= (or CD CASS) O)
   (not (and CD CASS))
   (= C RAD)
   (= CHAN C)
   (= FWBW C)
   (= V C)
   (= S C)
))

(assert TRAF)
(assert (and 
    (not (and C S P C ))
    (not (and C S P CASS (and CASS (not CD)) USB USB C ))
    (not (and C S P CASS (and CASS (not CD)) C ))
    (not (and C S P CD (and CD (not CASS)) C ))
))
(check-sat)