-- FILE: /home/diacon/LANG/Cafe/prog/debt-red.mod
-- CONTENTS: RWL specification of a debt reduction algorithm featuring
--           execution of algorithms in RWL,
--           execution modulo axioms, and 
--           formal verification of algorithm in RWL
-- AUTHOR: Razvan Diaconescu with some proofs by Michihiro Matsumoto
-- corrected by sawada@sra.co.jp
-- DIFFICULTY: **

set tram path brute .

in integer

-- specification of a system of debts data type
mod! DEBT (X :: DINT) {
  protecting(QID * { sort Qid -> Agent })

  [ Debt < Debt* ]

  op ___ : Agent DInt Agent -> Debt
  op nil : -> Debt*
  op __ : Debt* Debt* -> Debt* { assoc comm }

  vars a b c : Agent
  var n : DInt

-- the whole debt in the system
  op global-debt : Debt* -> DInt

  eq global-debt(nil) = 0 .
  ceq global-debt(a n b) = n   if 0 <= n .
  ceq global-debt(a n b) = - n if n <= 0 .
  eq global-debt(d1:Debt* d2:Debt*) = global-debt(d1) + global-debt(d2) .

-- individual balance for each agent
  op balance : Agent Debt* -> DInt

  eq balance(a, nil) = 0 .
  ceq balance(a, (b n c)) = 0   if  ((b =/= a) and (c =/= a)) or
                                    ( (b == a) and (c == a) ) . 
  ceq balance(a, (a n b)) = - n if b =/= a .
  ceq balance(a, (b n a)) = n   if b =/= a .
  eq balance(a, d1:Debt* d2:Debt*) = balance(a, d1) + balance(a, d2) . 
}

-- specification of the reduction algorithm
mod! DEBT-REDUCE {
  protecting(DEBT)

  var S : Debt*
  vars m n : DInt 
  vars !A !B !C : Agent

  eq nil S = S .

  ceq !A m !B = !B - m !A if (m < 0) .
  eq  !A 0 !B = nil .
  eq (!A m !B) (!A n !B) = !A (m + n) !B .
  eq !A m !A = nil .

  ctrans (!A m !B) (!B n !C) => (!A m !C) (!B (n - m) !C)
                                        if (m <= n) and (0 < m) and (0 < n) .
  ctrans (!A m !B) (!B n !C) => (!A (m - n) !B) (!A n !C)
                                        if (n <= m) and (0 < m) and (0 < n) .
}


-- ----------------------------------------------
-- some testing
-- ----------------------------------------------
view dint-int from DINT to INT {
  sort DInt -> Int,
  sort DNat -> Nat,
  op s X:DNat -> X:Nat + 1, 
  op p Y:DInt -> Y:Int - 1, 
  op 0 -> 0 
}

** need normalizations, setting `exec normalize on'. <- now this is obsolete switch
** system does normalize always.
-- set exec normalize on

open DEBT-REDUCE(dint-int) .
-- -------------------------------
let A = ('a -2 'b) ('a 3 'c) ('c 4 'b) .
red global-debt(A) .
red balance('b, A) .
exec A .
red A ==> ('a 1 'b) ('c 1 'b) .
-- -------------------------------
let B = ('a 4 'b) ('b 2 'c) ('d -4 'c) ('d 5 'b) ('a -1 'e)
        ('b 4 'e) ('b 3 'a) ('e 3 'd) .
set always memo on
-- tram exec B .
exec B .
--> this needs much time to perform ... please be patient
clean memo
-- eof
red B ==> 'c 2 'd .
**
-- eof

-- -------------------------------
--> the problem is NOT confluent: both of the following are normal forms
red ('c 3 'a) ('d 1 'a) ('a 2 'b) ==> ('d 1 'a) ('c 2 'b) ('c 1 'a) .
red ('c 3 'a) ('d 1 'a) ('a 2 'b) ==> ('c 2 'a) ('d 1 'b) ('c 1 'b) .
close

-- ------------------------------------------------------------
-- proof by induction in RWL 
-- global-debt(sys2) <= global-debt(sys1)   if sys1 ==> sys2
-- ------------------------------------------------------------

-- BASE CASE 
-- no transition:
open DEBT-REDUCE .
  ops sys1 sys2 : -> Debt* .
  eq sys2 = sys1 .
red global-debt(sys2) <= global-debt(sys1) .
close

mod* BASE { 
  pr(DEBT-REDUCE)

  ops a b c : -> Agent
  ops m n k : -> DNat

  eq 0 < m = true .
  eq 0 < n = true .
  eq 0 < k = true .
}

-- m < n
open BASE .
  eq k + m = n .
red global-debt((a m c) (b k c)) <= global-debt((a m b) (b n c)) .
close
-- m = n
open BASE .
  eq n = m .
red global-debt((a m c) (b 0 c)) <= global-debt((a m b) (b n c)) .
close
-- n < m
open BASE .
  eq n + k = m .
red global-debt((a k c) (b n c)) <= global-debt((a m b) (b n c)) .
close

-- INDUCTION STEP
open DEBT-REDUCE .
  ops sys1 sys2 a b : -> Debt* .
  eq global-debt(sys1) <= global-debt(sys2) = true .
  eq global-debt(a) <= global-debt(b) = true .
red global-debt(sys1 a) <= global-debt(sys2 b) .
close
--
eof
--
$Id: debt-red.mod,v 1.2 2010-08-04 04:37:34 sawada Exp $
