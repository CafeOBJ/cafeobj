** -*- Mode:CafeOBJ -*-

module! LIST(X :: TRIV)
     principal-sort List
{
  protecting (NAT)
  signature {
    [ Elt < NeList < List ]
    op nil : -> List {constr}
    op __ : List List -> List {constr assoc id: nil prec: 9}
    op __ : NeList List -> NeList  {r-assoc constr prec: 9}
    op |_| : List -> Nat 
    op head_ : NeList -> Elt {prec: 120}
    op tail_ : NeList -> List {prec: 120}
    pred empty?_ : List
  }
  axioms {
    eq | nil | = 0 .
    eq | E:Elt L:List | = 1 + | L | .
    eq | E:Elt | = 1 .
    eq head E:Elt L:List = E .
    eq tail E:Elt L:List = L .
    eq empty? L:List = L == nil .
  }
}

provide tiny-list

--
eof
--
$Id: tiny-list.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
