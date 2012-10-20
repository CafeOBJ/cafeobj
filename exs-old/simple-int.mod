** -*- Mode:CafeOBJ -*-
-- simple integer
--
require simple-nat ./simple-nat

module! SIMPLE-INT
{
  protecting (SIMPLE-NAT)
  signature {
    [ Nat NegInt < Int ]
    op -_ : NzNat -> NegInt
    op _+_ : Int Int -> Int
    op _-_ : Int Int -> Int
    op succ : Int -> Int
  }
  vars M M' : Int
}

provide simple-int
--
eof
--
$Id: simple-int.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
