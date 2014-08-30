-- FILE: /home/diacon/LANG/Cafe/prog/nat-omega.mod
-- CONTENTS: ADT specification of natural numbers with infinity
--           featuring extending importation mode and module sums
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: **

in simple-nat

mod! NAT-OMEGA {
  extending(BARE-NAT)

  op omega :  -> Nat
  pred _<=_ : Nat Nat 

  vars N M : Nat    
  
  eq 0 <= s(N) = true .
  cq s(M) <= s(N) = true     if M <= N .

  eq s(omega) = omega .
  eq N <= omega = true .
}

select NAT-OMEGA

red s s 0 <= s s s s 0 .
red s s 0 <= omega .
red omega <= s s 0 .
red omega <= omega .

open SIMPLE-NAT + NAT-OMEGA .
--> inductive proof of (SIMPLE-NAT + NAT-OMEGA) |= omega + N = omega
  eq omega + omega = omega .
-- n = 0
red omega + 0 == omega .
-- inductive hypothesis
  op n :  -> Nat . 
  eq omega + n = omega .
red omega + s(n) == omega .
-- on infinity
red omega + omega == omega .
close

-- adding the _+_ operation on infinity
mod! NAT-OMEGA+ {
  protecting(SIMPLE-NAT + NAT-OMEGA)

  eq omega + N:Nat = omega . 
}

select NAT-OMEGA+

red (s s 0) + (s 0) <= omega + s 0 .
--
eof
--
$Id: nat-omega.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
