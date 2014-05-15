mod! BARE-NAT {
  [ NzNat Zero < Nat ]
  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! TRIV+ (X :: TRIV) {
  op err :  -> ?Elt
}

-- list object
mod* B-LIST  {
  protecting (TRIV+)
  *[ List ]*
  op nil : -> List
  op cons : Elt List -> List {coherent}  -- method  {coherent}
  bop car : List -> ?Elt       -- attribute
  bop cdr : List -> List       -- method

  vars E E' : Elt
  var L : List

  eq car(nil) = err .
  eq car(cons(E, L)) = E .
  beq cdr(nil) = nil .
  beq cdr(cons(E, L)) = L .
}

open B-LIST .

ops l1 l2 : -> List .
ops e e' : -> Elt .
beq l1  = l2  .

-- red l1 .         -- okay
-- bred l1 .         -- okay
-- red l1 == l2 .  -- okay
-- red l1 =b= l2 .   -- okay
-- bred l1 == l2 .  -- okay
-- bred l1 =b= l2 .  -- okay

-- red cons(e,l1) .  -- okay
--> should be cons(e,l2) ??
bred cons(e,l1) . -- should be cons(e,l2) ??
-- eof
** 
red cons(e,l1) == cons(e,l2)  . -- okay
--> should be true ??
bred cons(e,l1) == cons(e,l2)  . -- should be true ??
--> should be true ??
red cons(e,l1) =b= cons(e,l2)  . -- should be true ??
--> should be true ??
bred cons(e,l1) =b= cons(e,l2)  . -- should be true ??

red cdr(cons(e,cons(e',l1))) . -- okay
--> should be cons(e',l2) ??
bred cdr(cons(e,cons(e',l1))) . -- should be cons(e',l2) ??

red car(cdr(nil)) . -- okay
red car(cdr(cons(e,l1))) . -- okay

close
