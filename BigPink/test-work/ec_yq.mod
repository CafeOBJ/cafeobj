** translated from OTTTER 3.05 example/auto/ec_yq.in
-- Equivalential calculus (EC): YQF -> YQL  (both are single axioms)
**

module EC-YQ (E :: TRIV)
{
  protecting (FOPL-CLAUSE)
  pred P : Elt
  op e : Elt Elt -> Elt
  vars x y z : Elt
  ax P(e(x,y)) & P(x) -> P(y) .
  ax P(e(e(x,y),e(e(x,z),e(z,y)))) .
}

option reset
flag(auto,on)
open EC-YQ .
ops a b c : -> Elt .
goal P(e(e(a,b),e(e(c,b),e(a,c)))) .
resolve .
close
--
eof

--
$Id:
