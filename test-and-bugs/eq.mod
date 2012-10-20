
module EQUAL 
{
  [ Elt ]
  op 0 : -> Elt
  op s_ : Elt -> Elt
  op _+_ : Elt Elt -> Elt { assoc comm id: 0 }
  op xif_then_else_fi : Bool Bool Bool -> Bool 
  op xif_then_else_fi : Elt Bool Bool -> Bool 
  op equal : Elt Elt -> Bool
  op eq* : Elt Elt -> Bool
  vars X Y : Elt
  eq s(X) + Y = s(X + Y) .
  -- 
  eq xif true then U:Bool else V:Bool fi = U .
  eq xif false then U:Bool else V:Bool fi = V .
  -- 
  eq equal(X,X) = true .
  eq equal(X,Y) = xif eq*(X, Y) then true else false fi .
  ceq eq* (X, Y) = true if X == Y .
  eq xif eq*(X, Y) then true else false fi = false .

}

module NEQUAL
{
  [ Elt ]
  op 0 : -> Elt
  op s_ : Elt -> Elt
  op if_then_else_fi : Bool Bool Bool -> Bool { strategy: (1 0) }
  op if_then_else_fi : Elt Bool Bool -> Bool { strategy: (1 0) }
  op nequal : Elt Elt -> Bool
  op neq* : Elt Elt -> Bool
  vars X Y : Elt
  eq nequal(X,X) = false .
  eq nequal(X,Y) = if neq*(X, Y) then true else false fi .
  ceq neq* (X, Y) = false if X == Y .
  eq if neq*(X, Y) then true else false fi = true .
}
