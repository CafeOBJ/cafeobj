** -*- Mode:CafeOBJ -*-
--> some simple theories, translated from OBJ3 examples.

module* TRIV* 
     principal-sort Elt
{
  [ Elt ]
  op * : -> Elt 
}

module* PREORD
     principal-sort Elt
{
  [ Elt ]
  op _<=_ : Elt Elt -> Bool 
  vars E1 E2 E3 : Elt 
  eq E1 <= E1 = true .
  cq E1 <= E3 = true if E1 <= E2 and E2 <= E3 .
}

module* POSET 
     principal-sort Elt
{
  [ Elt ]
  op _<_ : Elt Elt -> Bool 
  vars E1 E2 E3 : Elt 
  eq E1 < E1 = false .
  cq E1 < E3 = true if E1 < E2 and E2 < E3 .
}

module*  EQV
     principal-sort Elt
{
  [ Elt ]
  op _eq_ : Elt Elt -> Bool {comm}
  vars E1 E2 E3 : Elt 
  eq (E1 eq E1) = true .
  cq (E1 eq E3) = true if (E1 eq E2) and (E2 eq E3) .
}

module* MONOID 
     principal-sort M
{
  [ M ]
  op e : -> M 
  op _*_ : M M -> M {assoc id: e}
}

--
provide theories
--
eof
--
$Id: theories.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
