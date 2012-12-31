** translated from otter 3.0.5 examples/auto/x2_quant.in

-- % xx=e groups are commutative.
-- %

module X2 (E :: TRIV)
{
  protecting (FOPL-CLAUSE)

  op _*_ : Elt Elt -> Elt

  vars x y z : Elt
  ax \A[x,y]\A[z] (x * y) * z = x * (y * z) .

  ax \E[e:Elt] (\A[x] e * x = x) &
               (\A[x]\E[y] y * x = e) &
	       (\A[x] x * x = e) .
}

option reset
open X2 .
goal \A[x,y] x * y = y * x .

flag(auto,on)
flag(universal-symmetry,on)
resolve .
close
--
eof
--
$Id
