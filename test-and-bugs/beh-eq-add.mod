-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Thu, 25 Sep 97 03:57:06 GMT
-- Message-Id: <9709250357.AA09284@is27e0s07.jaist.ac.jp>
-- To: diacon@stoilow.imar.ro, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Subject:  bug related to the use of =*= ??
-- Content-Type: text
-- Content-Length: 1581

-- Dear Toshimi,

-- I think something is wrong with the use of =*=, maybe this is a bug
-- unless I am confused and miss something obvious.

-- Consider this specification:

mod* NNAT {
  protecting(NAT)

  *[ St ]*

  op _' : Nat -> St
  op _|_ : St St -> St
  bop _->_ : St Nat -> Bool

  vars S1 S2 : St
  vars M N : Nat

  eq M ' -> N = M == N .
  eq S1 | S2 -> N = S1 -> N or S2 -> N .
}

-- I am trying to do the following proof:

open NNAT .
  ops s1 s1' s2 s2' :  -> St .
  op n :  -> Nat .
--> s1 =*= s1' and s2 =*= s2'
   eq s1 =*= s1' = true .
   eq s2 =*= s2' = true .
red (s1 | s2) -> n == (s1' | s2') -> n . 
-- close

eof
-- ****************************************************************
and CafeOBJ gives

-- reduce in % : (s1 | s2) -> n == (s1' | s2') -> n
1>[1] rule: eq (S1:St | S2:St) -> N:Nat = S1:St -> N:Nat or S2:St 
       -> N:Nat
     { S1:St |-> s1, S2:St |-> s2, N:Nat |-> n }
1<[1] (s1 | s2) -> n --> s1 -> n or s2 -> n
1>[2] rule: eq (S1:St | S2:St) -> N:Nat = S1:St -> N:Nat or S2:St 
       -> N:Nat
     { S1:St |-> s1', S2:St |-> s2', N:Nat |-> n }
1<[2] (s1' | s2') -> n --> s1' -> n or s2' -> n
1>[3] rule: eq CXU == CYU = #!! (coerce-to-bool
                                    (term-equational-equal cxu cyu))
     { CXU |-> s1 -> n or s2 -> n, CYU |-> s1' -> n or s2' -> n }
1<[3] (s1 -> n or s2 -> n) == (s1' -> n or s2' -> n) --> false
false : Bool
(0.020 sec for parse, 3 rewrites(0.050 sec), 29 match attempts)

But I think the reduction is somehow blocked since one can do 2 more
steps and get "true" by using

    ceq hs1:St -> vs1:Nat = hs2:St -> vs1:Nat if hs1:St =*= hs2:St .

Why this doesnt happen?

Thanks,
Razvan


