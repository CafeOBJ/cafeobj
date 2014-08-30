-- FILE: /home/diacon/LANG/Cafe/prog/bset.mod
-- CONTENTS: behavioural specification of a set object featuring
--           use of coherence operations, 
--           simplicity of behavioural proofs, and
--           object refinement
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

mod* BASICSETS (X :: TRIV) {
  -- protecting(PROPC)

  *[ Set ]*

  op empty : -> Set 
  op add   : Elt Set -> Set    -- method {coherent}
  bop _in_  : Elt Set -> Bool  -- attribute

  vars E E' : Elt
  var S : Set 

  eq E in add(E', S) = (E == E') or (E in S) .
  eq E in empty = false .
}

** proof score for  behavioural coherence of add(_)
open BASICSETS .
  ops e e' :  -> Elt .
  ops s s' :  -> Set .
** hypothesis
  beq s = s' .
** behavioural coherence of add(_) by case analysis
red e  in add(e, s)  == e  in add(e, s') .
red e' in add(e, s)  == e' in add(e, s') .
close

mod* BASICSETS+ { protecting (BASICSETS)
  op add   : Elt Set -> Set  {coherent}
}

mod* SETS {
  protecting(BASICSETS+)
  
  op _U_ : Set Set -> Set  -- {coherent}
  op _&_ : Set Set -> Set  -- {coherent}
  op not : Set -> Set      -- {coherent}

  var E : Elt
  vars S1 S2 : Set
    
  eq E in S1 U S2  = (E in S1)  or (E in S2) .
  eq E in S1 & S2  = (E in S1) and (E in S2) .
  eq E in not(S1)  = not (E in S1) .
}

** proof score for beh coherence of _U_, _&_, and not(_)
open SETS .
  ops s1 s2 s1' s2' : -> Set .
  op e : -> Elt .
** by theorem of constants
  ceq S1 =*= S2 = true if (e in S1) == (e in S2) .
** hypothesis
  beq s1 = s1' .
  beq s2 = s2' .
** beh coherence of _U_
red (s1 U s2) =*= (s1' U s2') .
** beh coherence of _&_
red (s1 & s2) =*= (s1' & s2') .
** beh coherence of not_
red (not(s1)) =*= (not(s1')) .
close

mod* SETS+ { protecting (SETS)
  op _U_ : Set Set -> Set   {coherent}
  op _&_ : Set Set -> Set   {coherent}
  op not : Set -> Set       {coherent}
}

** *************************** ***
**> Some behavioral properties ***
** *************************** ***
open SETS+ .
  op e : -> Elt .
  ops s1 s2 s3 : -> Set .
** by theorem of constants
  ceq S1:Set =*= S2:Set = true if (e in S1) == (e in S2) .
**> commutativity of _U_
red (s1 U s2) =*= (s2 U s1) .
**> associativity of _U_
red (s1 U (s2 U s3)) =*= ((s1 U s2) U s3) .
**> idempotency of _U_
red (s1 U s1) =*= s1 .
**> empty is the unity of _U_
red (empty U s1) =*= s1 .
**> commutativity of _&_
red (s1 & s2) =*= (s2 & s1) .
**> associativity of _&_
red (s1 & (s2 & s3)) =*= ((s1 & s2) & s3) .
**> idempotency of _&_
red (s1 & s1) =*= s1 .
**> empty & S is empty
red (empty & s1) =*= empty .
**> distributivity
red (s1 & (s2 U s3)) =*= ((s1 & s2) U (s1 & s3)) .
red (s1 U (s2 & s3)) =*= ((s1 U s2) & (s1 U s3)) .
**> de Morgan laws
red (not(s1 U s2)) =*= (not(s1) & not(s2)) . 
red (not(s1 & s2)) =*= (not(s1) U not(s2)) . 
**> double negation
red (not(not(s1))) =*= s1 .
close

-- ==============================================================
-- REFINEMENT of the BASIC-SET object by LIST object
-- ==============================================================

mod! TRIV+ (X :: TRIV) {
  op err :  -> ?Elt 
}

-- the list object
mod* LIST  {
  protecting (TRIV+)

  *[ List ]*

  op nil : -> List   
  op cons : Elt List -> List   {coherent}  -- method
                                           -- provable from the rest of spec 
  bop car : List -> ?Elt       -- attribute
  bop cdr : List -> List       -- method
    
  vars E E' : Elt
  var L : List

  eq car(nil) = err .
  eq car(cons(E, L)) = E .
  beq cdr(nil) = nil .
  beq cdr(cons(E, L)) = L .
}

-- LIST refines BASICSETS+ via the morphism
-- add    |--> cons
-- E in L |--> (E == car(L)) or-else (car(L) =/= err  and-also  E in cdr(L))

mod* LIST' {
  protecting (LIST)
-- a derived attribute   
  op _in_ : Elt List -> Bool  {coherent}
                              -- coherence provable from the rest of spec 
  vars E E' : Elt
  var L : List

  eq E in L = (E == car(L)) or-else (car(L) =/= err  and-also  E in cdr(L)) .
}

open LIST'(NAT) .
red 1 in cons(2,cons(3,cons(4,nil))) .
red 1 in cdr(cons(1,cons(2,cons(3,cons(4,nil))))) .
red 1 in cdr(cons(1,cons(2,cons(3,cons(4,cons(1,nil)))))) .
close

-- proof that LIST refines BASICSETS
open LIST' .
  ops e e1 e2 : -> Elt .
  op l : -> List .
-- basic cases 
  eq e1 in l = true .
  eq e2 in l = false .
-- case analysis
red e  in nil       == false .
red e1 in cons(e,l) == true  .
red e2 in cons(e,l) == false .
red e  in cons(e,l) == true  .
close 
--
eof
--
$Id: bset.mod,v 1.2 2007-02-05 04:44:54 sawada Exp $
