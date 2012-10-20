-- Subject: an example and a question
-- Date: Tue, 23 Sep 97 09:14:33 -0500
-- From: Dorel Lucanu <dlucanu@thor.infoiasi.ro>
-- X-Mailer: E-Mail Connection v2.5.02
-- Content-Type: text
-- Content-Length: 2635

-- -- [ From: Dorel Lucanu * EMC.Ver #2.5.02 ] --

-- Dear Toshimi,

-- Below is another example of the mutual exclusion problem. Please look a bit
-- to the last reduction. It is similar to that we discussed  at RJ97.  My
-- question is if there exists any possibility to get the expected value false.

-- Best regards,
-- Dorel.


-- **********************************************************************
module Net {
       [Place < Marking]
       signature {
         op _+_ : Marking Marking -> Marking { assoc comm }
       }
}

module N1ab {
        protecting(Net)
        signature {
          ops sa1 sa2 sc sb1 sb2 :  -> Place
          ops ya2 sa6 :  -> Place
          ops yb2 sb6 :  -> Place
	}
        axioms {
-- preserved rules
          trans [ta1] : sa1 => sa2 .
          trans [tb1] : sb1 => sb2 .
-- first refinement 
          trans [ta2] : sa2 + sc => ya2 + sa6 .
          trans [ta5] : ya2 + sa6 => sa1 + sc .
-- second refinement 
          trans [tb2] : sb2 + sc => yb2 + sb6 .
          trans [tb5] : yb2 + sb6 => sb1 + sc .
        }
}

-- ******************************************************************
open N1ab
--> prove the correctnes of the refinement
red (sa2 + sc) ==> (sa1 + sc) . -- it should be true
red (sb2 + sc) ==> (sb1 + sc) . -- it should be true
--> A can enter its critical section
red (sa2 + sc + sb2) ==> (ya2 + sa6 + sb2) . -- it should be true
--> B can enter its critical section
red (sa2 + sc + sb2) ==> (sa2 + yb2 + sb6) . -- it should be true
--> A and B cannot enter simultaneously their critical sections
red (sa2 + sc + sb2) ==> (ya2 + sa6 + yb2 + sb6) . -- it should be false
close
eof
-- ****************************************************************************
*
--> prove the correctnes of the refinement
-- reduce in % : sa2 + sc ==> sa1 + sc
true : Bool
(0.010 sec for parse, 14 rewrites(0.100 sec), 112 match attempts)
-- reduce in % : sb2 + sc ==> sb1 + sc
true : Bool
(0.010 sec for parse, 14 rewrites(0.100 sec), 112 match attempts)
--> A can enter its critical section
-- reduce in % : sa2 + sc + sb2 ==> ya2 + sa6 + sb2
true : Bool
(0.010 sec for parse, 12 rewrites(0.400 sec), 125 match attempts)
--> B can enter its critical section
-- reduce in % : sa2 + sc + sb2 ==> sa2 + yb2 + sb6
true : Bool
(0.010 sec for parse, 120 rewrites(2.300 sec), 1141 match attempts)
--> A and B cannot enter simultaneously their critical sections
-- reduce in % : sa2 + sc + sb2 ==> ya2 + sa6 + yb2 + sb6
sa2 + sc + sb2 ==> ya2 + sa6 + yb2 + sb6 : Bool
(0.010 sec for parse, 1212 rewrites(28.060 sec), 14094 match attempts)
-- ****************************************************************************
*****

