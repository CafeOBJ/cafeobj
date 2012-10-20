** -*- Mode:CafeOBJ -*-
**> an example of CafeOBJ higher order map.
**> 
module! LIST'(X :: TRIV)
{
  [ Elt < NeList < List ]
  op nil : -> List 
  op _,_ : List List -> List {assoc id: nil}
  op _,_ : NeList List -> NeList {r-assoc}
}

module* FUN(X :: TRIV, Y :: TRIV) {
  op f_ : Elt.X -> Elt.Y
}

module! MAP( X :: TRIV,
	     Y :: TRIV,
	     L1 :: LIST'[X],
	     L2 :: LIST'[Y],
	     F  :: FUN[X,Y])
{
  op map_ : List.L1 -> List.L2
  var E : Elt.X
  var L : List.L1
  eq map nil = nil .
  eq map(E, L) = (f E), (map L) .
}

module! DOUBLE {
  protecting (NAT)
  op double_ : Nat -> Nat
  var N : Nat
  eq double(N) = N + N .
}

make MAP-double (MAP[X <= NAT,
                     Y <= NAT,
	             F <= DOUBLE{ op f_ -> double_ }])
   
select MAP-double
red map nil .
red map(1, 2, 3, 4) .
show .
--
eof
**
$Id: horder-map.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
