** commutativity
** works
module TEST2
{
  [ Elt ]
  op _*_ : Elt Elt -> Elt
  op 1 : -> Elt
  op - : Elt -> Elt

  vars x y z : Elt
  eq (x * y) * z = x * (y * z) .
  eq 1 * x = x .
  eq x * 1 = x .
  eq -(x) * x = 1 .
  eq x * -(x) = 1 .
  eq x * x = 1 .
}

open TEST2 .
protecting (FOPL-CLAUSE)
option reset
flag(auto,on)
param(max-proofs,1)
goal \A[X:Elt, Y:Elt] X * Y = Y * X .
resolve .
close
-- 
eof
--
$Id
