
module FACT {
  protecting (RAT)
  op _! : Nat -> NzNat
  eq 0 ! = 1 .
  ceq N:Nat ! = N * (N - 1 !) if N > 0 .
}

provide Mfact
eof
-- examples
select FACT
parse (4 / 2)! .
reduce (4 / 2)! .
reduce (4 / 3)! .

** $Id: Mfact.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
