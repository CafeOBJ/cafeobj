** from example of OTTER3.0.5 examples/group.in
-- Search for a complete set of reductions for free groups.
--
module GRP (E :: TRIV)
{
  op f : Elt Elt -> Elt
  op g : Elt -> Elt
  op e : -> Elt
  vars x y z : Elt
  eq f(e,x) = x .
  eq f(g(x),x) = e .
  eq f(f(x,y),z) = f(x,f(y,z)) .
}

option reset
open GRP .
protecting (FOPL-CLAUSE)
flag(auto, on)
flag(universal-symmetry,on)
resolve .
close
--
eof
--
$Id:
