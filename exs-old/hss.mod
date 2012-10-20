module* HSS (X :: TRIV)
{
  *[ Hss ]*
  bop put : Elt Hss -> Hss
  bop rest : Hss -> Hss
  bop get : Hss -> Elt

  var S : Hss
  var E : Elt

  eq get(put(E, S)) = E .
  beq rest(put(E,S)) = S .
}

module PROOF1 {
  protecting (HSS + NAT)
  
  bop rest* : Hss Nat -> Hss
    
  vars S S1 S2 : Hss
  vars N N' : Nat
  var E : Elt

  eq [p1]: rest*(S, s(N)) = rest*(rest(S), N) .
  eq [p2]: rest*(S, 0) = S .
}
