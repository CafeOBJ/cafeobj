require Msimple-nat

module LIST-OF-NAT {
  protecting (SIMPLE-NAT)
  [ Nat < NeList < List ]
  -- constructors
  op nil : -> List { constr }
  op __ : List List -> List { assoc id: nil constr }
  op __ : NeList List -> NeList { r-assoc constr }
  -- selectors
  op head_ : NeList -> Nat
  op tail_ : NeList -> List 
  var N : Nat  var L : List 
  eq head(N L) = N .
  eq tail(N L) = L .
}

provide Mlist-of-nat
eof
--
select LIST-OF-NAT
set trace on
reduce 0 nil s(0) nil s(s(0)) .
reduce head(0 s(0) s(s(0))) .
reduce tail(0 s(0) s(s(0))) .
reduce tail(nil 0 s(0) nil s(s(0))) .

** $Id: Mlist-of-nat.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
