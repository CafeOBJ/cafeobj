require Mone

module LIST (X :: ONE) {
  [ Elt < NeList < List ]
  op nil : -> List
  op __ : Elt List -> NeList
  op __ : Elt NeList -> NeList
  op head_ : List -> Elt
  op tail_ : List -> List
  var E : Elt
  var L : List
  eq head (E L) = E .
  eq tail (E L) = L .
}

provide Mlist

eof

** $Id: Mlist.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
