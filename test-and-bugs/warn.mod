-- From: Diaconescu Razvan <diacon@stoilow.imar.ro>
-- Message-Id: <9711091521.AA05434@stoilow.imar.ro>
-- To: sawada@sra.co.jp
-- Subject:  strange warnings?
-- Content-Type: text
-- Content-Length: 1290

-- Toshimi,

-- I think the system gives sometimes some strange warnings related to
-- the sub-sorting mechanism. However I maybe miss something, so please
-- let me know if I am confused.

-- Consider the following:

mod! STRG(X :: TRIV) {
  [ Elt < Strg ]

  op _._ : Strg Strg -> Strg { assoc }
  op null :  -> Strg 

  eq null . S:Strg = S .
  eq S:Strg . null = S .
}

mod! SORTING-STRG {
  protecting(STRG(NAT)* { sort Nat -> Elt })

  ctrans N:Elt . N':Elt => N' . N 
     if (N' < N) .
}

mod! SORTING-STRG-PROOF {
  protecting(SORTING-STRG)
  -- op disorder : Strg -> Nat 
  -- op _>>_ : Elt Strg -> Nat

  op disorder : Strg -> NzNat 
  op _>>_ : Elt Strg -> NzNat

  vars E E' : Elt 
  var S : Strg 
    
  eq disorder(null) = 0 .
  eq disorder(E) = 0 .
  eq disorder(E . S) = disorder(S) + (E >> S) .

  eq E >> null = 0 .
  cq E >> E' = 0 if E <= E' .
  cq E >> E' = 1 if E' < E  .
  cq E >> (E' . S) = s(E >> S) if E' <  E .
  cq E >> (E' . S) = (E >> S)  if E <= E' .
}

-- defining module! SORTING-STRG-PROOF
-- [Warning]: redefining module SORTING-STRG-PROOF ....._..
-- [Warning]: axiom : disorder(E . S) = disorder(S) + (E >> S)
--            contains error operators, should be used with care!.....
-- [Warning]: axiom : E >> (E' . S) = s (E >> S) if E' < E
--            contains error operators, should be used with care!...* done.
-- -----------
