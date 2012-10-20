-- -*- Mode: CafeOBJ -*-
-- Date: Fri, 22 Aug 1997 13:11:17 +0300
-- From: Diaconescu Razvan <diacon@stoilow.imar.ro>
-- Message-Id: <9708221011.AA02110@stoilow.imar.ro>
-- To: dlucanu@infoiasi.ro, mitihiro@jaist.ac.jp, nakagawa@sra.co.jp,
--        s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Subject:  transitions example: a bug and a nice th proving problem
-- Cc: ghstef@imar.ro, kokichi@jaist.ac.jp, vec@funinf.math.unibuc.ro
-- Content-Type: text
-- Content-Length: 4906
--
-- I have now a rather interesting example of RWL specification featuring
-- various aspects of transitions in CafeOBJ. This is about a system of
-- debts between economical agents. A transition between the states of
-- such a system means a simpification by cancelation of mutual
-- debts. This is a realistic example where transitions are meaningful.

-- I give you the code, and then I point out a serious bug in the actual
-- version of CafeOBJ (for Sawada-san) and then I would like to propose
-- some nice theorem proving problems. Please run this example by
-- yourself.
--

-- CODE:
-- -----------------------------------------
mod! DEBT {
  protecting(INT)
  protecting(QID * { sort Id -> Agent })

  [ Debt < Debt* ]

  op ___ : Agent Nat Agent -> Debt
  op nil : -> Debt*
  op __ : Debt* Debt* -> Debt* { assoc comm }

  vars a b c : Agent
  var n : Nat

-- the whole debt in the system
  op global-debt : Debt* -> Nat

  eq global-debt(nil) = 0 .
  eq global-debt(a n b) = n .
  eq global-debt(d1:Debt* d2:Debt*) = global-debt(d1) + global-debt(d2) .

-- individual balance for each agent
  op balance : Agent Debt* -> Int

  ceq balance(a, (b n c)) = 0   if  ((b =/= a) and (c =/= a)) or
                                    ((b == a)  and  (c == a)) . 
  ceq balance(a, (a n b)) = - n if b =/= a .
  ceq balance(a, (b n a)) = n   if b =/= a .
  eq balance(a, d1:Debt* d2:Debt*) = balance(a, d1) + balance(a, d2) . 
}

mod! DEBT-REDUCE {
  protecting(DEBT)

  var S : Debt*
  vars m n : Nat 
  vars !A !B !C : Agent

  eq nil S = S .

  trans !A 0 !B => nil .
  trans (!A m !B) (!A n !B) => !A (m + n) !B .
  trans !A m !A => nil .
  ctrans (!A m !B) (!B n !C) => (!A m !C) (!B (n - m) !C)
                                        if (m <= n) .
  ctrans (!A m !B) (!B n !C) => (!A (m - n) !B) (!A n !C)
                                        if (n <= m) .

}

open DEBT-REDUCE .

let A = ('a 2 'b) ('b 2 'c) .

red global-debt(A) .
red balance('b, A) .
exec A .
exec ('a 2 'b) ('b 2 'c) ('c 4 'd) ('d 5 'b) ('e 1 'a) ('b 3 'e) ('e 4 'd) .

red A ==> ('a 2 'c) .
close
-- ----------------------------------------------------------
eof

BUG: Just look at the last reduction

red A ==> ('a 4 'c) . ---> ('a 2 'c) .

This should give true in a rather simple way. But look at the trace:

-- reduce in % : ('a 2 'b) ('b 2 'c) ==> 'a 4 'c
1>[1] apply trial #1
 -- rule: ceq CXU ==> CYU = true if CXU = ( * ) => CYU
     { CXU |-> ('a 2 'b) ('b 2 'c), CYU |-> 'a 4 'c }
2>[1] rule: eq CXU = ( N:Nat* ) => CYU = #!! (coerce-to-bool
                                              (term-pattern-included-in-cexec
                                               cxu cyu n))
      { CXU |-> ('a 2 'b) ('b 2 'c), N:Nat* |-> *, CYU |-> 'a 4 'c
       }
3>[1] apply trial #2
   -- rule: ctrans (!A:Agent m:Nat !B:Agent) (!B:Agent n:Nat !C:Agent)
          => (!A:Agent m:Nat !C:Agent) (!B:Agent n:Nat - m:Nat !C:Agent)
          if m:Nat <= n:Nat
       { n:Nat |-> 2, !C:Agent |-> 'c, !A:Agent |-> 'a, m:Nat |-> 
          2, !B:Agent |-> 'b }
4>[1] rule: eq NN:NzNat <= NM:NzNat = #! (<= nn nm)
        { NN:NzNat |-> 2, NM:NzNat |-> 2 }
4<[1] 2 <= 2 --> true
3>[2] match success #2
3<[2] ('a 2 'b) ('b 2 'c) --> ('a 2 'c) ('b 2 - 2 'c)
3>[3] apply trial #3
   -- rule: ctrans (!A:Agent m:Nat !B:Agent) (!B:Agent n:Nat !C:Agent)
          => (!A:Agent m:Nat - n:Nat !B:Agent) (!A:Agent n:Nat !C:Agent)
          if n:Nat <= m:Nat
       { n:Nat |-> 2, !C:Agent |-> 'c, !A:Agent |-> 'a, m:Nat |-> 
          2, !B:Agent |-> 'b }
4>[3] rule: eq NN:NzNat <= NM:NzNat = #! (<= nn nm)
        { NN:NzNat |-> 2, NM:NzNat |-> 2 }
4<[3] 2 <= 2 --> true
3>[4] match success #3
3<[4] ('a 2 'b) ('b 2 'c) --> ('a 2 - 2 'b) ('a 2 'c)
2<[5] ('a 2 'b) ('b 2 'c) = ( * ) => 'a 4 'c --> false
1>[6] rewrite rule exhausted (#1)
('a 2 'b) ('b 2 'c) ==> 'a 4 'c : Bool
(0.000 sec for parse, 5 rewrites(0.090 sec), 34 match attempts)

It seems CafeOBJ doesnt reduce  2 - 2 to 0, and then ('a 0 'b) to
nil. I dont understand why it stops here. Anyway, I think whatever
reason for this stop, it should somehow go ahead and infer this rather
simple sentence.
-------------------------------------------------------

PROBLEM: I would like to propose the following problems to be
solved. I am ready to offer a reward for a nice proof score (a bottle
of good Romanian wine)!

1. balance(agnt, sys1) == balance(agnt, sys2)  if  sys1 ==> sys2 .
             
2. global-debt(sys1) <= global-debt(sys2)  if sys1 ==> sys2

for each agent "agnt" and debt systems "sys1" and "sys2". These two
sentences say something about the correctness of the behaviour of this
concurrent system. These are inductive properties, please think about
them and lets prove them.

The success of for such proofs would be a real test for the
verification capabilities of the actual system, and I am sure that
trying to solve these problems will lead to improving the transition
related part of CafeOBJ.

Have fun!
Razvan


