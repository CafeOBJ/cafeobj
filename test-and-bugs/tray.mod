module* ONE {
  [ Elt ] 
}

module* STACK (X :: ONE) {
  [ Stack ]
  op push : Elt Stack -> Stack
}

module TRAY (Y :: STACK) {
  [ Tray ]
  op tray : Stack Stack -> Tray
  ops in-tray out-tray : Tray -> Stack
  op in : Elt Tray -> Tray 
  var E : Elt
  vars S S' : Stack
  eq in(E, tray(S,S')) = tray(push(E,S),S') .
  trans tray(push(E,S),S') => tray(S, push(E, S')) .
  eq in-tray(tray(S,S')) = S .
  eq out-tray(tray(S,S')) = S' .
}

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

view LIST-AS-STACK from STACK to LIST {
  sort Stack -> NeList
  op push -> __
}

module LIST-TRAY {
  protecting (TRAY(Y <= LIST-AS-STACK))
}

module NAT-TRAY {
  protecting (TRAY(X.Y <= view to SIMPLE-NAT { sort Elt -> Nat }))
}

--
eof




