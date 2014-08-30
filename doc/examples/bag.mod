-- FILE: /home/diacon/LANG/Cafe/prog/bag.mod
-- CONTENTS: behavioural specification of bags featuring use of
--           coherent methods
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

-- user-defined naturals
mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

-- naturals with a predecesor function
mod! BARE-NATP {
  protecting(BARE-NAT)

  op p_ : Nat -> Nat

  eq p 0 = 0 .
  eq p s N:Nat = N .
}

red in BARE-NATP : p s s p p s 0 .

--> version with PUT and TAKE as bop methods: 
mod* BAG(X :: TRIV) {
  protecting(BARE-NATP)
  
  *[ Bag ]*

  op empty :  -> Bag 
  bop put : Elt Bag -> Bag    -- method 
  bop take : Elt Bag -> Bag   -- method
  bop get : Bag Elt -> Nat    -- attribute

  vars E E' : Elt
  var B : Bag 

  eq get(empty, E) = 0 .
  cq get(put(E, B), E')  =  get(B, E')   if E =/= E' .
  eq get(put(E, B), E)   = s(get(B, E)) . 
  cq get(take(E, B), E') =  get(B, E')   if E =/= E' .
  eq get(take(E, B), E)  = p(get(B, E)) .
}

--> proof that =*= is hidden congruence
-- the system cannot prove it by itself because of the case analysis
open BAG .
  ops b1 b2 :  -> Bag .
  ops e e' :  -> Elt .
  var E : Elt 
-- hypothesis
  eq get(b1, E) = get(b2, E) .
-- case e =/= e'
red get(put(e, b1), e') == get(put(e, b2), e') .
red get(take(e, b1), e') == get(take(e, b2), e') .
-- case e == e'
red get(put(e, b1), e) == get(put(e, b2), e) .
red get(take(e, b1), e) == get(take(e, b2), e) .
close

--> version with PUT and TAKE as coherent methods
mod* BAG(X :: TRIV) {
  protecting(BARE-NATP)
  
  *[ Bag ]*

  op empty :  -> Bag 
  op put : Elt Bag -> Bag    
  op take : Elt Bag -> Bag   
  bop get : Bag Elt -> Nat  -- attribute

  vars E E' : Elt
  var B : Bag 

  eq get(empty, E) = 0 .
  cq get(put(E, B), E')  =  get(B, E')   if E =/= E' .
  eq get(put(E, B), E)   = s(get(B, E)) . 
  cq get(take(E, B), E') =  get(B, E')   if E =/= E' .
  eq get(take(E, B), E)  = p(get(B, E)) .
}

--> proof that coherence of put & take is a consequence of the rest of spec
open BAG .
  ops b1 b2 :  -> Bag .
  ops e  e' :  -> Elt .
  var E : Elt 
-- hypothesis
  eq get(b1, E) = get(b2, E) .
-- case e =/= e'
red get(put(e, b1), e') == get(put(e, b2), e') .
red get(take(e, b1), e') == get(take(e, b2), e') .
-- case e == e'
red get(put(e, b1), e) == get(put(e, b2), e) .
red get(take(e, b1), e) == get(take(e, b2), e) .
close

mod* BAG+ { protecting (BAG)
  op put  : Elt Bag -> Bag    {coherent}
  op take : Elt Bag -> Bag    {coherent}
}	    

--> take(e', put(e, b)) =*= put(e, take(e', b))
-- open .
open BAG+ .
  ops e e' e1 :  -> Elt .
  op b :  -> Bag .
red get(take(e', put(e, b)), e1) == get(put(e, take(e', b)), e1) .
red get(take(e', put(e, b)), e) == get(put(e, take(e', b)), e) .
red get(take(e', put(e, b)), e') == get(put(e, take(e', b)), e') .
--> take(e, put(e, b)) is NOT beh equiv to put(e, take(e, b))
red get(take(e, put(e, b)), e) == get(put(e, take(e, b)), e) .
close
eof
--
$Id: bag.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
