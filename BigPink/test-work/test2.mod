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
-- flag(very-verbose,on)
-- flag(trace-demod,on)
-- flag(print-kept,on)
param(max-proofs,1)
let g = \A[X:Elt, Y:Elt] X * Y = Y * X .
goal g .
resolve .
close
**
eof
**
$Id
