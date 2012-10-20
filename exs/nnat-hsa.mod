-- FILE: /home/diacon/LANG/Cafe/prog/nnat-hsa.mod
-- CONTENTS: behavioural specification of non-deterministic natural numbers
--           featuring use of coherent operations for non-determinism
--           handling in behavioural specification
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

-- non-deterministic naturals
mod* NNAT-HSA {
  protecting(NAT)

  *[ NNat ]*

  op [_] : Nat -> NNat
  op _|_ : NNat NNat -> NNat {r-assoc}  -- coherent 
  bop _->_ : NNat Nat -> Bool

  vars S1 S2 : NNat
  vars M N : Nat

  eq [M] -> N = M == N .
  eq S1 | S2 -> N = S1 -> N or S2 -> N .
}

select NNAT-HSA
--> some tests
red ( [1] | [2] | [3] ) -> 2 .
red ( [1] | [2] | [3] ) -> 4 .

--> the behavioural equivalence is =*=
--  (already automatically proved by the system)  
--> s =*= s' == (forall n:Nat) s -> n iff s' -> n

--> proof of coherence of _|_ 
open NNAT-HSA .
  ops s1 s1' s2 s2' :  -> NNat .
  op n :  -> Nat .
-- hypothesis: s1 =*= s1' and s2 =*= s2'
  var N : Nat
  eq s1 -> N = s1' -> N .
  eq s2 -> N = s2' -> N .
red (s1 | s2) -> n == (s1' | s2') -> n . 
close

mod* NNAT-HSA+
{
  protecting (NNAT-HSA)
  op _|_ : NNat NNat -> NNat   {coherent}
}		 

-- proof of some behavioural properties of the non-deterministic constructor
open NNAT-HSA+ .
  ops s1 s2 s3 :  -> NNat .
  op n :  -> Nat . 
--> proof of commutativity
red (s1 | s2) -> n == (s2 | s1) -> n .
--> proof of associativity
red ((s1 | s2) | s3) -> n == (s1 | (s2 | s3)) -> n .
--> proof of idempotence
--> by lemma on idempotence on or
  eq B:Bool or B = B .
red (s1 | s1) -> n == s1 -> n .
close

-- adding the _<=_ predicate to the non-deterministic naturals
-- first a simpler version 
mod* NNAT-HSA<= {
  protecting(NNAT-HSA+)

  bop _<=_ : NNat Nat -> Bool

  vars M N : Nat 
  vars S1 S2 : NNat 
    
  eq [M] <= N = M <= N .
  eq S1 | S2 <= N = S1 <= N and S2 <= N .
}

select NNAT-HSA<=

red ([1] | ([2] | [3])) <= 3 .
red ([1] | ([2] | [3])) <= 1 .

-- the fully general version of _<=_
mod* NNAT-HSA<=< {
  protecting(NNAT-HSA)

  op _<=_ : NNat NNat -> Bool
    
  vars M N : Nat 
  vars S1 S2 S : NNat 

  eq [M] <= [N] = M <= N .
  eq S1 | S2 <= S = (S1 <= S) and (S2 <= S) .
  eq S <= S1 | S2 = (S <= S1) and (S <= S2) .
}

select NNAT-HSA<=<

red ([1] | ([2] | [3])) <= ([4] | ([4] | [5])) .
red ([1] | ([2] | [3])) <= ([4] | ([4] | [2])) .

--
eof
--
$Id: nnat-hsa.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
