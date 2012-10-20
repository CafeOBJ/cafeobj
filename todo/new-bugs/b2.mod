-- 
-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Wed, 13 May 98 12:05:19 JST
-- Message-Id: <9805130305.AA07253@is27e0s07.jaist.ac.jp>
-- To: diacon@stoilow.imar.ro, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Subject:  old bug again in behavioural reduction? 
-- Content-Type: text
-- Content-Length: 3087

-- Dear Toshimi,

-- It seems to me that the reduction with beq is not done correctly. This
-- is a bit surprising since I tought that a version released a couple of
-- month ago solved this problem which seems to appear again in 1.4.1p5
-- which I am using now.

-- This is the example:

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! TRIV+ {
  protecting(TRIV)

  [ Elt < Elt+ ]
  
  op err :  -> Elt+ 
}

mod* BUF  (X :: TRIV+) {

  *[ Buf ]*

  op init :  -> Buf 
  op put : Elt Buf -> Buf -- {coherent}
  bop get_ : Buf -> Elt+
  bop take_ : Buf -> Buf 
  bop empty? : Buf -> Bool

  var E : Elt
  var B : Buf 
        
  eq empty?(init) = true .
  cq empty?(take B) = true if empty?(B) .
  eq empty?(put(E, B)) = false .

  beq take put(E, B) = put(E, take B) .

  eq get (take B) = get B .
  eq get init = err .
  cq get put(E, B) = E if empty?(B) .
  cq get put(E, B) = get B if not empty?(B) .
}

-- -----------------------------------------------------
-- BEHAVIOURAL EQUIVALENCES
-- -----------------------------------------------------
mod* BUF-BEQ {
  protecting(BUF + BARE-NAT)

  op _R[_]_ : Buf Nat Buf -> Bool {coherent}

  bop take : Nat Buf -> Buf 

  var N : Nat 
  vars B B1 B2 : Buf 

  eq take(0, B) = B .
  eq take(s(N), B) = take(N, take B) .

  eq B1 R[N] B2 = get take(N, B1)     == get take(N, B2)  and
                  empty?(take(N, B1)) == empty?(take(N, B2)) .
}

-- -----------------------------------------------------
-- BEHAVIOURAL COHERENCE PROOFS
-- -----------------------------------------------------

-- for put : Elt Buf -> Buf
open BUF-BEQ .
  ops b1 b2 :  -> Buf .
  op n :  -> Nat .
  op e :  -> Elt .
-- hypothesis
  beq b1 = b2 .
-- conclusion
red put(e, b1) R[n] put(e, b2) .

eof

This gives true just by applying b1 --> b2 by violating the beh
context condition. 

-- reduce in %(X.BUF) : put(e,b1) R [ n ] put(e,b2)
1>[1] rule: eq B1:Buf R [ N:Nat ] B2:Buf = get take(N:Nat,B1:Buf)
       == get take(N:Nat,B2:Buf) and empty?(take(N:Nat,B1:Buf)) ==
       empty?(take(N:Nat,B2:Buf))
    { B1:Buf |-> put(e,b1), N:Nat |-> n, B2:Buf |-> put(e,b2) }
1<[1] put(e,b1) R [ n ] put(e,b2) --> get take(n,put(e,b1)) == get
     take(n,put(e,b2)) and empty?(take(n,put(e,b1))) == empty?(take(
    n,put(e,b2)))
1>[2] rule: beq b1 = b2
    {}
1<[2] b1 --> b2
1>[3] rule: eq CXU == CYU = #!! (coerce-to-bool
                                    (term-equational-equal cxu cyu))
    { CXU |-> get take(n,put(e,b2)), CYU |-> get take(n,put(e,b2)
       ) }
1<[3] get take(n,put(e,b2)) == get take(n,put(e,b2)) --> true
1>[4] rule: eq CXU == CYU = #!! (coerce-to-bool
                                    (term-equational-equal cxu cyu))
    { CXU |-> empty?(take(n,put(e,b2))), CYU |-> empty?(take(n,put(
       e,b2))) }
1<[4] empty?(take(n,put(e,b2))) == empty?(take(n,put(e,b2))) --> 
    true
1>[5] rule: eq [ident2] : true and X-ID:Bool = X-ID:Bool
    { X-ID:Bool |-> true }
1<[5] true and true --> true
true : Bool

Please let me know if this is due rather to some confusion from my
side...
---
Best regards,
Razvan








