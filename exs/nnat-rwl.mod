-- FILE: /home/diacon/LANG/Cafe/prog/nnat-rwl.mod
-- CONTENTS: RWL specification of non-deterministic natural numbers
--           featuring the use of the built-in semantic transition
--             predicate ==>
-- AUTHOR: Jose Meseguer with proof by Razvan Diaconescu
-- DIFFICULTY: **

mod! NNAT {
  extending(NAT)

  op _|_ : Nat Nat -> Nat  {assoc}
   
  vars M N : Nat

  trans N | M => N .
  trans N | M => M .
}

--> proof of 3 <= ( 4 | 4 | 5 )
red in NNAT : (3 <= ( 4 | 4 | 5 ))  ==> true .

--
eof
--
$Id: nnat-rwl.mod,v 1.2 2010-07-30 04:20:08 sawada Exp $
