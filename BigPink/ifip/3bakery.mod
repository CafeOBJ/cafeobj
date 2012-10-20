-- the natural numbers

mod! NATNUM {
  ** protecting(FOPL-CLAUSE)
  [ NatNum ]
  op 0 : -> NatNum
  op s : NatNum -> NatNum
  pred _<_ : NatNum NatNum
  vars M N : NatNum
  ax ~(s(M) < M) .
  ax [SOS1]: ~(s(M) = 0) .
  ax [SOS]: M < s(M) .
  ax [SOS]: 0 < s(M) .
  ax ~(s(M) = M) .
  ax [SOS]: M = 0 | 0 < M .
  ax ~(0 < M)| ~(M = 0) . 
  ax ~(M = N & M < N) .
  ax ~(M < N & N < M) .
  ax ~(M < 0) .
}

-- the program counters
mod! STATUS {
  protecting(FOPL-CLAUSE)
  [ Status ]
  ops non-CS wait CS : -> Status
  var S : Status
}

-- customers
mod* CUSTOMER1 {
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
  ax stat1(run1(C,M))= wait -> stat1(C) = non-CS | stat1(C) = wait .
  ax stat1(C) = non-CS -> ticket1(run1(C,M)) = s(M) .
  ax stat1(C) = wait & (M = 0 | ~(M < ticket1(C))) -> stat1(run1(C,M)) = CS .
  ax stat1(run1(C,M)) = CS -> stat1(C) = wait .
  ax stat1(C) = wait & ~(M = 0) & M < ticket1(C) -> stat1(run1(C,M)) = wait .
  ax stat1(C) = wait -> ticket1(run1(C,M)) = ticket1(C) .
  ax (stat1(C) = CS) = (stat1(run1(C,M)) = non-CS) .
  ax stat1(C) = CS -> ticket1(run1(C,M)) = 0 .
}

mod* CUSTOMER2 {
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
  ax stat2(run2(C,M))= wait -> stat2(C) = non-CS | stat2(C) = wait .
  ax stat2(C) = non-CS -> ticket2(run2(C,M)) = s(M) .
  ax stat2(C) = wait & (M = 0 | ticket2(C) < M) -> stat2(run2(C,M)) = CS .
  ax stat2(run2(C,M)) = CS -> stat2(C) = wait .
  ax stat2(C) = wait & ~(M = 0) & ~(ticket2(C) < M) -> stat2(run2(C,M)) = wait .
  ax stat2(C) = wait -> ticket2(run2(C,M)) = ticket2(C) .
  ax (stat2(C) = CS) = (stat2(run2(C,M)) = non-CS) .
  ax stat2(C) = CS -> ticket2(run2(C,M)) = 0 .
}

-- bakery algorithm
mod* SHOP {
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
  var S : Shop
  eq Init = shop(init1,init2) .
  beq Run1(shop(C1,C2)) = shop(run1(C1,ticket2(C2)),C2) .
  beq Run2(shop(C1,C2)) = shop(C1,run2(C2,ticket1(C1))) .
--  beq Run(shop(C1,C2)) = shop(run1(C1,ticket2(C2)),run2(C2,ticket1(C1))) .
  eq Stat1(shop(C1,C2)) = stat1(C1) .
  eq Stat2(shop(C1,C2)) = stat2(C2) .
  eq Ticket1(shop(C1,C2)) = ticket1(C1) .
  eq Ticket2(shop(C1,C2)) = ticket2(C2) .
}

mod* PROOF {

protecting(SHOP)

op c1 : -> Customer1 .
op c2 : -> Customer2 .

pred P : Shop .
#define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .

}

option reset
-- flag(auto3,on)
flag(process-input, on)

-- flag(print-kept, off)
-- flag(print-new-demod, off)
-- flag(print-back-demod, off)
-- flag(print-back-sub, off)
flag(control-memory, on)
param(max-sos, 250)
param(pick-given-ratio, 4)
param(stats-level, 1)
-- param(max-seconds, 86400)
flag(kb2, on)
-- flag(para-from, off)
-- flag(para-into, on)
-- flag(para-from-right, off)
-- flag(para-into-right, off)
-- flag(para-from-vars, off)
-- flag(eq-units-both-ways, on)
-- flag(dynamic-demod-all, on)
-- flag(dynamic-demod, on)
-- flag(order-eq, on)
-- flag(back-demod, on)
-- flag(lrpo, on)
flag(back-unit-deletion, on)

-- param(control-memory-point,100)

flag(hyper-res, on)
flag(unit-deletion, on)
flag(factor, on)

-- flag(meta-paramod, on)
flag(prop-res, on)
-- flag(neg-hyper-res, on)
-- flag(order-hyper, on)
-- flag(binary-res, on)
-- flag(no-new-demod, on)
-- flag(para-into-vars, on)

flag(universal-symmetry,on)
flag(dist-const,on)
flag(quiet,on)
flag(print-proofs,off)
flag(print-stats,on)
param(max-proofs,1)
param(max-given,87)
param(max-seconds,3)

-- flag(randomize-sos,off)
flag(input-sos-first,on)

open PROOF

-- db reset

-- lex(*,SKOLEM)
lex(*, Init,Run1,Run2,Stat1,Stat2,Ticket1,Ticket2, SKOLEM)

sos = { :SYSTEM-GOAL }

check inv P of shop(c1,c2) from Init

close


**
eof
