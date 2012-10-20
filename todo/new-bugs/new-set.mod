-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Thu, 28 May 98 17:36:42 JST
-- Message-Id: <9805280836.AA04223@is27e0s07.jaist.ac.jp>
-- To: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Subject:  behavioural sets and lists revised
-- Cc: goguen@cs.ucsd.edu
-- Content-Type: text
-- Content-Length: 2656

-- Dear Colleagues,

-- Yesterday, while revising the personal CafeOBJ library, I spent some
-- time on the behavioural sets and lists example and came up with an
-- interesting new version of this story.

-- The main point in this new version is that I prove that simple
-- beh list object (so *without* the _in_ attribute) is a refinement of
-- the beh set object. I felt that in the previous version _in_ on lists
-- was there only in order to make the refinement possible, but the
-- current version shows that we dont need this.

-- I also did some changes in the CafeOBJ Jewels in order to reflect this
-- improvement. This latest version of the paper can be downolaed from my
-- home page.

-- I hope you can enjoy the beauty of this approach.

-- Have fun,
-- Razvan
-- -------------------------------------------
mod* BASICSETS (X :: TRIV) {
  protecting(PROPC)

  *[ Set ]*

  op empty : -> Set 
  op add   : Elt Set -> Set    {coherent} -- method 
  bop _in_  : Elt Set -> Bool  -- attribute

  vars E E' : Elt
  var S : Set 

  eq E in add(E', S) = (E == E') or (E in S) .
  eq E in empty = false .
}

-- ==============================================================
-- REFINEMENT of the BASICSETS object by LIST object
-- ==============================================================

mod! TRIV+ (X :: TRIV) {
  op err :  -> ?Elt 
}

-- the list object
mod* LIST {
  protecting(TRIV+)

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

-- LIST refines BASICSETS via the morphism
-- add    |--> cons
-- E in L |--> (E == car(L)) or-else (car(L) =/= err  and-also  E in cdr(L))

mod* LIST' {
  protecting(LIST)
-- a derived attribute   
  op _in_ : Elt List -> Bool  {coherent}
                              -- coherence provable from the rest of spec 
  vars E E' : Elt
  var L : List

  eq E in L = (E == car(L)) or-else (car(L) =/= err  and-also  E in cdr(L)) .
}

select LIST'(NAT) .
red 1 in cons(2,cons(3,cons(4,nil))) .
red 1 in cdr(cons(1,cons(2,cons(3,cons(4,nil))))) .
red 1 in cdr(cons(1,cons(2,cons(3,cons(4,cons(1,nil)))))) .

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



