-- Date: Wed, 8 Oct 97 18:31:33 JST
-- Message-Id: <9710080931.AA00171@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  another instantiation problem
-- Content-Type: text
-- Content-Length: 800

-- Toshimi,

-- Here is maybe another bug in the instantiation mechanism:

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! SIMPLE-NAT {
  protecting(BARE-NAT)

  op _+_ : Nat Nat -> Nat 
  
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . eq 0 + N:Nat = N .
}

mod* MON* (Y :: TRIV) {
  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

view bare-nat from TRIV to BARE-NAT { sort Elt -> Nat }

view nat;to+ from MON*(bare-nat) to SIMPLE-NAT {
  op _;_ -> _+_,
  op null -> 0
}    

-- This gives an error:

-- -- defining view nat;to+ ,,,,,,_,,
-- [Error]: Operator mapping is not injective, the declaration
--          null :  -> Nat
--          has no proper image in the target.

-- Do you know why?

-- Thanks,
-- Razvan
