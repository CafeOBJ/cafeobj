** -*- Mode:CafeOBJ -*-

module! NAT' {
  [ Pos < Nat ]
  op 0 : -> Nat 
  op 1 : -> Pos 
  op s_ : Nat -> Pos 
  eq 1 = s 0 .
  op _<=_ : Nat Nat -> Bool 
  vars M N : Nat 
  eq M <= M = true .
  eq s M <= 0 = false .
  eq 0 <= M = true .
  eq s M <= s N = M <= N .
}

module! LIST2(E :: TRIV) {
  [ NeList < List ]
  op nil : -> List
  op cons : Elt List -> NeList 
  op car_ : NeList -> Elt 
  op cdr_: NeList -> List 
  var E : Elt 
  var L : List 
  eq car cons(E,L) = E .
  eq cdr cons(E,L) = L .
}

module! NTH(E :: TRIV) {
  protecting (LIST2[E] + NAT')
  [ Elt < ErrElt ]
  op length_ : List -> Nat 
  op nth : Pos List -> Elt 
  op toolong : -> ErrElt 
  var E : Elt 
  var L : List
  eq length nil = 0 .
  eq length cons(E,L) = s length L .
  var P : Pos 
  eq nth(P,nil) = toolong .
  eq nth(s 0,cons(E,L)) = E .
  eq nth(s P,cons(E,L)) = nth(P,L) .
}

module* FN 
     principal-sort Elt
{
  [ Elt ]
  op f : Elt -> Elt 
}

module! MAP(F :: FN) {
  protecting (NTH(F))
  op map_ : List -> List 
  var E : Elt 
  var L : List
  eq map nil = nil .
  eq map cons(E,L) = cons(f(E),map L) .
}

module! SETUPFN
     principal-sort Elt
{
  [ Elt ]
  op f : Elt -> Elt 
}

module! SETUP 
{
  extending (MAP(SETUPFN))
  op e : -> Elt 
  op l : -> List
  op p : -> Pos 
  var P : Pos 
  ceq nth(P,map l) = f(nth(P,l)) if P <= length l .
  eq p <= length l = true .
}

**> base case
select SETUP
reduce nth(1,map cons(e,nil)) == f(nth(1,cons(e,nil))) .

**> induction step, by case analysis on P: Pos
reduce nth(1,map cons(e,l)) == f(nth(1,cons(e,l))) .
reduce nth(s p,map cons(e,l)) == f(nth(s p,cons(e,l))) .

**> thus we can assert:
module! MAP-FACT(F :: FN) {
  protecting (MAP[F])
  var L : List 
  var P : Pos 
  ceq nth(P, map L) = f(nth(P,L)) if P <= length L .
}

show MAP-FACT

--
eof
**
$Id: map.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $ 
--
