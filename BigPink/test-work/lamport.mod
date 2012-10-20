-- the natural numbers
module! NATNUM 
{
  protecting (FOPL-CLAUSE)
  [ NatNum ]
  op 0 : -> NatNum
  op s : NatNum -> NatNum
  op _<=_ : NatNum NatNum -> Bool
  op _<_ : NatNum NatNum -> Bool
  vars M N : NatNum
  ax ~(M <= N) | ~(N < M) .
}

-- the program counters
module! STATUS
{
  protecting (FOPL-CLAUSE)
  [ Status ]
  ops non-CS please wait CS : -> Status
  var S : Status
  ax ~(non-CS = please) .
  ax ~(non-CS = wait) .
  ax ~(non-CS = CS) .
  ax ~(please = wait) .
  ax ~(please = CS) .
  ax ~(wait = CS) .
  ax S = non-CS | S = please | S = wait | S = CS .
}

-- customers
module* CUSTOMER1
{
  protecting (FOPL-CLAUSE)
  protecting (NATNUM + STATUS)
  *[ Customer1 ]*
  op init1 : -> Customer1
  -- attribures
  bop ticket1 : Customer1 -> NatNum 
  bop stat1 : Customer1 -> Status
  -- methods
  bop run1 : Customer1 NatNum -> Customer1
  var C : Customer1 var M : NatNum
  eq stat1(init1) = non-CS .
  eq ticket1(init1) = 0 .
  ceq stat1(run1(C,M)) = please if stat1(C) == non-CS .
  ceq ticket1(run1(C,M)) = s(0) if stat1(C) == non-CS .
  ceq stat1(run1(C,M)) = wait if stat1(C) = please .
  ceq ticket1(run1(C,M)) = s(M) if stat1(C) == please .
  ceq stat1(run1(C,M)) = CS
      if (stat1(C) == wait) and ((M == 0) or (ticket1(C) <= M)) .
  ceq ticket1(run1(C,M)) = ticket1(C)
      if (stat1(C) == wait) and ((M == 0) or (ticket1(C) <= M)) .
  ceq run1(C,M) = C
      if (stat1(C) == wait) and not ((M == 0) or (ticket1(C) <= M)) .
  ceq stat1(run1(C,M)) = non-CS if stat1(C) == CS .
  ceq ticket1(run1(C,M)) = 0 if stat1(C) == CS .
}

module* CUSTOMER2
{
  protecting (FOPL-CLAUSE)
  protecting (NATNUM + STATUS)
  *[ Customer2 ]*
  op init2 : -> Customer2
  -- attribures
  bop ticket2 : Customer2 -> NatNum 
  bop stat2 : Customer2 -> Status
  -- methods
  bop run2 : Customer2 NatNum -> Customer2
  var C : Customer2 var M : NatNum
  eq stat2(init2) = non-CS .
  eq ticket2(init2) = 0 .
  ceq stat2(run2(C,M)) = please if stat2(C) == non-CS .
  ceq ticket2(run2(C,M)) = s(0) if stat2(C) == non-CS .
  ceq stat2(run2(C,M)) = wait if stat2(C) = please .
  ceq ticket2(run2(C,M)) = s(M) if stat2(C) == please .
  ceq stat2(run2(C,M)) = CS
      if (stat2(C) == wait) and ((M == 0) or (ticket2(C) < M)) .
  ceq ticket2(run2(C,M)) = ticket2(C)
      if (stat2(C) == wait) and ((M == 0) or (ticket2(C) < M)) .
  ceq run2(C,M) = C
      if (stat2(C) == wait) and not ((M == 0) or (ticket2(C) < M)) .
  ceq stat2(run2(C,M)) = non-CS if stat2(C) == CS .
  ceq ticket2(run2(C,M)) = 0 if stat2(C) == CS .
}

-- bakery algorithm
module* SHOP
{
  protecting (CUSTOMER1 + CUSTOMER2)
  *[ Shop ]*
  op shop : Customer1 Customer2 -> Shop { coherent }
  op cust1 : Shop -> Customer1 { coherent }
  op cust2 : Shop -> Customer2 { coherent }
  bop Run1 : Shop -> Shop
  bop Run2 : Shop -> Shop 
  bop Stat1 : Shop -> Status
  bop Stat2 : Shop -> Status
  bop Ticket1 : Shop -> NatNum
  bop Ticket2 : Shop -> NatNum
  op Init : -> Shop
  var C1 : Customer1 var C2 : Customer2 var S : Shop
  eq Init = shop(init1,init2) .
  eq shop(cust1(S), cust2(S)) = S .
  eq cust1(shop(C1,C2)) = C1 .
  eq cust2(shop(C1,C2)) = C2 .
  beq Run1(shop(C1,C2)) = shop(run1(C1,ticket2(C2)), C2) .
  beq Run2(shop(C1,C2)) = shop(C1,run2(C2,ticket1(C1))) .
  eq Stat1(shop(C1,C2)) = stat1(C1) .
  eq Stat2(shop(C1,C2)) = stat2(C2) .
  eq Ticket1(shop(C1,C2)) = ticket1(C1) .
  eq Ticket2(shop(C1,C2)) = ticket2(C2) .
  eq Ticket1(Run2(S)) = Ticket1(S) .
  eq Ticket2(Run1(S)) = Ticket2(S) .
  eq Stat1(Run2(S)) = Stat1(S) .
  eq Stat2(Run1(S)) = Stat2(S) .

}

open SHOP .

protecting (FOPL-CLAUSE)

db reset
option reset
-- flag(quiet,on)
flag(auto,on)
flag(print-stats,on)
flag(universal-symmetry,on)
-- param(max-weight,12)
param(max-proofs,1)

--
var C1 : Customer1

-- ax (stat1(C1) = non-CS | (stat1(C1) = please) | (stat1(C1) = wait) | stat1(C1) = CS .
-- ax (stat2(C2) = non-CS | (stat2(C2) = please) | (stat2(C2) = wait) | stat2(C2) = CS .

pred P : Shop .

-- #define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .
#define P(S:Shop) ::= (Tickets1(S) = 0) -> (Stat1(S) = non-CS | Stat1(S) = please) .
-- #define P(S:Shop) ::= (Stat1(S) = CS) -> (Stat2(S) = wait | Ticket2(S) = 0 | Ticket(S) <= Ticket2(S)) .

-- goal P(Init) .
-- goal \A[S:Shop] P(S) -> P(Run1(S)) .
-- goal \A[S:Shop] P(S) -> P(Run2(S)) .

check invariance P from Init

-- goal \A[C1:Customer1]\A[C2:Customer2] P(shop(C1,C2)) -> P(Run1(shop(C1,C2))) .

-- resolve .
close

-- reduce Stat1 Run1 Run2 Run2 Run1 Run1 Run2 Run1 init .
-- reduce Stat2 Run1 Run2 Run2 Run1 Run1 Run2 Run1 init .

--
eof
**
$Id:
