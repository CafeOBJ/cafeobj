require Mone

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

provide Mtray

eof

** $Id: Mtray.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
