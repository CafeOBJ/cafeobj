-- FILE: /home/diacon/LANG/Cafe/prog/simple-nat.mod
-- CONTENTS: ADT specification of natural numbers with addition and
--           multiplication
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: *

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! SIMPLE-NAT {
  protecting(BARE-NAT)

  op _+_ : Nat Nat -> Nat {comm}
  
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . 
}

red in SIMPLE-NAT : (s s 0) + (s s 0) .

mod! TIMES-NAT {
  protecting(SIMPLE-NAT)

  op _*_ : Nat Nat -> Nat

  vars M N : Nat 
    
  eq 0 * N = 0 .
  eq N * 0 = 0 .
  eq N * s(M) = (N * M) + N .
}

red in TIMES-NAT : (s s s 0) * (s s s s s 0) .
--
eof
--
$Id: simple-nat.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
