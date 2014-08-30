-- FILE: /home/diacon/LANG/Cafe/prog/blist.mod
-- CONTENTS: behavioural specification of a list object featuring
--           use of coherence operations
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! TRIV+ (X :: TRIV) {
  op err :  -> ?Elt 
}

-- list object
mod* LIST  {
  protecting (TRIV+)

  *[ List ]*

  op nil : -> List   
  op cons : Elt List -> List   -- method  {coherent}
  bop car : List -> ?Elt       -- attribute
  bop cdr : List -> List       -- method
    
  vars E E' : Elt
  var L : List

  eq car(nil) = err .
  eq car(cons(E, L)) = E .
  beq cdr(nil) = nil .
  beq cdr(cons(E, L)) = L .
}

select LIST(NAT) .

red car(cons(1, nil)) .
red car(cdr(cons(1,nil))) .	 
red car(cdr(cdr(cons(1, nil)))) .

-- behavioural equivalence on lists
mod* LIST-BEQ {
  protecting(LIST + BARE-NAT)
-- 2nd order cdr function on List
  bop cdr : Nat List -> List

  eq cdr(0, L:List) = L .
  eq cdr(s(N:Nat), L:List) = cdr(N, cdr(L)) .
-- behavioural equivalence relation 
  op _R[_]_ : List Nat List -> Bool {coherent}

  eq L:List R[N:Nat] L':List = car(cdr(N, L)) == car(cdr(N, L')) . 
}

-- proof of coherence of cons
open LIST-BEQ .
  op n :  -> Nat .
  ops l1  l2  :  -> List  .
  op e :  -> Elt .
** hypothesis
  beq l1  = l2  .
** proof by case analysis 
red cons(e, l1) R[0]   cons(e, l2) .
red cons(e, l1) R[s n] cons(e, l2) .

close

mod* LIST+ { protecting (LIST)
  op cons : Elt List -> List   {coherent}
}	     
mod* LIST+-BEQ { pr(LIST-BEQ + LIST+) }

--
eof
--
$Id: blist.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
