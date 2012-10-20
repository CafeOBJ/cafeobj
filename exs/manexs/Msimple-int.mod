require Msimple-nat

module SIMPLE-INT {
  protecting (SIMPLE-NAT)
  [ Nat NegInt < Int ]
  op -_ : NzNat -> NegInt
  op _+_ : Int Int -> Int
  op _-_ : Int Int -> Int
  op s : Int -> Int
  vars M M' : Int
}

provide Msimple-int

eof
** $Id: Msimple-int.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
