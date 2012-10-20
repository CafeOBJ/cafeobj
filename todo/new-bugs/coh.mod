-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- CONTENTS: behavioural specification of bags featuring use of
--           coherent methods
-- AUTHOR: Razvan Diaconescu and Kokichi Futatsugi
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

--> test for BARE-NATP:
red in BARE-NATP : p s s p p s 0 .

--> a version with PUT and TAKE as bop methods: 
mod* BAG1(X :: TRIV) {
  protecting(BARE-NATP)
  
  *[ Bag ]*

  op empty :  -> Bag		-- initial bag 

  bop put : Elt Bag -> Bag	-- method 
  bop take : Elt Bag -> Bag	-- method
  bop get : Bag Elt -> Nat	-- attribute

  vars E E' : Elt
  var B : Bag 

  eq get(empty, E) = 0 .
  cq get(put(E, B), E')  =  get(B, E')   if E =/= E' .
  eq get(put(E, B), E)   =  s(get(B, E)) . 
  cq get(take(E, B), E') =  get(B, E')   if E =/= E' .
  eq get(take(E, B), E)  =  p(get(B, E)) .
}

--> Let's define an equicalance ralation
--> "(_=*=_) : Bag Bag -> Bool" as follows:
--> (bag1 =*= bag2) =def= ((\all E : Elt) (get(bag1,E) == get(bag2,E))).
--> This =*= *is* a behavioral congruence relation.
--> The CafeOBJ interpreter cannot prove it automatically because of the
--> case analysis for defining "get".  Notice that conditonal
--> equations are used to define "get" operation.
--> But, it is easily proved as follows, if the case analysis is done
--> by users.

open BAG1 .
  ops b1 b2 :  -> Bag .
  ops e e' :  -> Elt .
  var E : Elt 
--> hypothesis
  eq get(b1, E) = get(b2, E) .
--> case e =/= e'
red get(put(e, b1), e') == get(put(e, b2), e') .
red get(take(e, b1), e') == get(take(e, b2), e') .
--> case e == e'
red get(put(e, b1), e) == get(put(e, b2), e) .
red get(take(e, b1), e) == get(take(e, b2), e) .
close

--> A version with "put" and "take" as coherent methods.
--> This is based on the fact that "put" and "take" are coherent.
--> That is, congruence with respect to behavioral equivalence; this
--> will be proved later.

mod* BAG2(X :: TRIV) {
  protecting(BARE-NATP)
  
  *[ Bag ]*

  op empty :  -> Bag 
  op put : Elt Bag -> Bag	-- methods (coherent)
  op take : Elt Bag -> Bag	-- methods (coherent)
  bop get : Bag Elt -> Nat	-- attribute

  vars E E' : Elt
  var B : Bag 

  eq get(empty, E) = 0 .
  cq get(put(E, B), E')  =  get(B, E')   if E =/= E' .
  eq get(put(E, B), E)   = s(get(B, E)) . 
  cq get(take(E, B), E') =  get(B, E')   if E =/= E' .
  eq get(take(E, B), E)  = p(get(B, E)) .
}

--> In the case of BAG2, the CafeOBJ interpreter can prove
--> automatically that =*= is a behavioral congruence relation.
--> But this is based on the following proof!

--> Proof of the fact that put & take is a consequence of the rest of
--> spec.
open BAG2 .
  ops b1 b2 :  -> Bag .
  ops e  e' :  -> Elt .
  var E : Elt 
--> hypothesis
  eq get(b1, E) = get(b2, E) .
--> case e =/= e'
red get(put(e, b1), e') == get(put(e, b2), e') .
red get(take(e, b1), e') == get(take(e, b2), e') .
--> case e == e'
red get(put(e, b1), e) == get(put(e, b2), e) .
red get(take(e, b1), e) == get(take(e, b2), e) .
close

mod* BAG+ { pr(BAG2)
  op put  : Elt Bag -> Bag    {coherent}
  op take : Elt Bag -> Bag    {coherent}
}	    

--> take(e', put(e, b)) =*= put(e, take(e', b)) does not hold if e' = e
--> open .
open BAG+
  ops e e' e1 :  -> Elt .
  op b :  -> Bag .
red get(take(e', put(e, b)), e1) == get(put(e, take(e', b)), e1) .
red get(take(e', put(e, b)), e) == get(put(e, take(e', b)), e) .
red get(take(e', put(e, b)), e') == get(put(e, take(e', b)), e') .
--> take(e, put(e, b)) is NOT beh equiv to put(e, take(e, b))
red get(take(e, put(e, b)), e) == get(put(e, take(e, b)), e) .
close
