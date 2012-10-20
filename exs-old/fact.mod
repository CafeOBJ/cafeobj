** -*- Mode:CafeOBJ -*-

module! FACT {
  protecting (RAT)
  op _! : Nat -> NzNat
  op fact : Nat -> NzNat
  eq 0 ! = 1 .
  eq N:NzNat ! = N * (p N !) .
  eq fact(0) = 1 .
  eq fact(N:NzNat) = N * fact(p N) .
}

select FACT
--> try the followings
red 10 ! .
red 1 + 2 + 3 + 4 + 5 + 6  ! .
red 0 ! .
red 40 / 5 ! .
red (5 * 8)/ 5 ! .
--
eof
**
$Id: fact.mod,v 1.1.1.1 2003-06-19 08:30:15 sawada Exp $
