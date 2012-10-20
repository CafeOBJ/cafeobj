-- ------------------------------------------------------------------------
-- (Ebakery.mod)
-- -----------------------------------------------------------------------

-- the natural numbers
mod! NATNUM
{
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  op 0 : -> NatNum
  op s : NatNum -> NatNum
  pred _<_ : NatNum NatNum  -- { meta-demod }
  vars M N : NatNum
  ax ~(s(M) < M) .
  ax ~(s(M) = 0) .
  ax [SOS]: M < s(M) .
  ax [SOS]: 0 < s(M) .
  ax ~(s(M) = M) .
  ax [SOS]: M = 0 | 0 < M .
  ax ~(0 < M)| ~(M = 0) . 
  ax ~(M = N & M < N) .
  ax ~(M < N & N < M) .
  ax ~(M < 0) .
--  ax (s(M) = s(N)) = (M = N) .
--  ax (s(M) < s(N)) = (M < N) .
  ax M = M .
}

-- the program counters
mod! STATUS
{
  protecting(FOPL-CLAUSE)
  [ Status ]
  ops non-CS wait CS error : -> Status
  var S : Status

--  ax (non-CS = please) = false .
--  ax (please = non-CS) = false .
--  ax (non-CS = wait) = false .
--  ax (wait = non-CS) = false .
--  ax (non-CS = CS) = false .
--  ax (CS = non-CS) = false .
--  ax (please = wait) = false .
--  ax (wait = please) = false .
--  ax (please = CS) = false .
--  ax (CS = please) = false .
--  ax (wait = CS) = false .
--  ax (CS = wait) = false .

--  ax ~(S = non-CS) | ~(S = please) . 
--  ax ~(S = non-CS) | ~(S = wait) . 
--  ax ~(S = non-CS) | ~(S = CS) . 
--  ax ~(S = please) | ~(S = wait) . 
--  ax ~(S = please) | ~(S = CS) . 
--  ax ~(S = wait) | ~(S = CS) . 

  ax (S = S) = true .
}

-- customers
mod* CUSTOMER1
{
  protecting(NATNUM + STATUS)
  *[ Customer1 ]*
  op init1 : -> Customer1
  -- attributes
  bop ticket1 : Customer1 -> NatNum
  bop stat1 : Customer1 -> Status
  -- methods
  bop run1 : Customer1 NatNum -> Customer1
  vars C C1 : Customer1  vars M N : NatNum
  eq stat1(init1) = non-CS .
  eq ticket1(init1) = 0 .
  ax stat1(C) = non-CS -> stat1(run1(C,M))= wait .
  ax stat1(run1(C,M))= wait -> stat1(C) = non-CS .
  ax stat1(C) = non-CS -> ticket1(run1(C,M)) = s(M) .
  ax stat1(C) = wait & (M = 0 | ~(M < ticket1(C))) -> stat1(run1(C,M)) = CS .
  ax stat1(run1(C,M)) = CS -> stat1(C) = wait .
  ax stat1(C) = wait & ~(M = 0) & M < ticket1(C) -> stat1(run1(C,M)) = error .
  ax stat1(run1(C,M)) = error -> stat1(C) = wait .
  ax stat1(C) = wait -> ticket1(run1(C,M)) = ticket1(C) .
  ax (stat1(C) = CS) = (stat1(run1(C,M)) = non-CS) .
  ax stat1(C) = CS -> ticket1(run1(C,M)) = 0 .
}

mod* CUSTOMER2
{
  protecting(NATNUM + STATUS)
  *[ Customer2 ]*
  op init2 : -> Customer2
  -- attributes
  bop ticket2 : Customer2 -> NatNum
  bop stat2 : Customer2 -> Status
  -- methods
  bop run2 : Customer2 NatNum -> Customer2
  vars C C1 : Customer2  var M : NatNum
  eq stat2(init2) = non-CS .
  eq ticket2(init2) = 0 .
  ax stat2(C) = non-CS -> stat2(run2(C,M))= wait .
  ax stat2(run2(C,M))= wait -> stat2(C) = non-CS .
  ax stat2(C) = non-CS -> ticket2(run2(C,M)) = s(M) .
  ax stat2(C) = wait & (M = 0 | ticket2(C) < M) -> stat2(run2(C,M)) = CS .
  ax stat2(run2(C,M)) = CS -> stat2(C) = wait .
  ax stat2(C) = wait & ~(M = 0) & ~(ticket2(C) < M) -> stat2(run2(C,M)) = error .
  ax stat2(run2(C,M)) = error -> stat2(C) = wait .
  ax stat2(C) = wait -> ticket2(run2(C,M)) = ticket2(C) .
  ax (stat2(C) = CS) = (stat2(run2(C,M)) = non-CS) .
  ax stat2(C) = CS -> ticket2(run2(C,M)) = 0 .
}

-- bakery algorithm
mod* SHOP
{
  protecting(CUSTOMER1 + CUSTOMER2)
  *[ Shop ]*
  op shop : Customer1 Customer2 -> Shop { coherent }
  bop Run1 : Shop -> Shop
  bop Run2 : Shop -> Shop
--  bop Run : Shop -> Shop
  bop Stat1 : Shop -> Status
  bop Stat2 : Shop -> Status
  bop Ticket1 : Shop -> NatNum
  bop Ticket2 : Shop -> NatNum
  op Init : -> Shop
  vars C1 D1 : Customer1   vars C2 D2 : Customer2
  var S : Shop   var B : Bool
  ax B = B .
  eq Init = shop(init1,init2) .
  beq Run1(shop(C1,C2)) = shop(run1(C1,ticket2(C2)),C2) .
  beq Run2(shop(C1,C2)) = shop(C1,run2(C2,ticket1(C1))) .
--  beq Run(shop(C1,C2)) = shop(run1(C1,ticket2(C2)),run2(C2,ticket1(C1))) .
  eq Stat1(shop(C1,C2)) = stat1(C1) .
  eq Stat2(shop(C1,C2)) = stat2(C2) .
  eq Ticket1(shop(C1,C2)) = ticket1(C1) .
  eq Ticket2(shop(C1,C2)) = ticket2(C2) .
}

mod* PROOF
{

  protecting(SHOP)

  op c1 : -> Customer1 .
  op c2 : -> Customer2 .

  pred P : Shop .
  #define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .

}

option reset
flag(kb2, on)
flag(back-unit-deletion, on)
flag(hyper-res, on)
flag(prop-res,off)
flag(unit-deletion, on)
flag(factor, on)
flag(universal-symmetry,off)
flag(dist-const,on)
flag(input-sos-first,on)
flag(quiet,on)
flag(print-stats,on)
param(stats-level, 1)
param(max-proofs,1)
param(pick-given-ratio,4)
-- 
param(max-given,46)
-- param(max-seconds,2)

open PROOF .
db reset

-- sos = { SOS :SYSTEM-GOAL }
sos = { :SYSTEM-GOAL }

check inv P of shop(c1,c2) from Init

close

**
eof
**
$Id: Ebakery.mod,v 1.2 2003-11-04 03:11:26 sawada Exp $
