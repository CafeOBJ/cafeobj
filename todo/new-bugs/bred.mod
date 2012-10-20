mod* BLIST {
  [ Elt ]
  op err : -> ?Elt
  *[ List ]*
  op nil : -> List
  bop cons : Elt List -> List
  bop car : List -> ?Elt
  bop cdr : List -> List
  var E : Elt
  var L : List
  eq car(nil) = err .
  eq car(cons(E, L)) = E .
  beq cdr(nil) = nil .
  beq cdr(cons(E, L)) = L .
}
