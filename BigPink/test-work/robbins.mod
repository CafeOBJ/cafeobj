** translated from otter 3.0.5 examples auto/robbins.in
-- % Robbins algebra
-- %
-- % If a Robbins algebra has an element c such that x+c=c,
-- % then it is Boolean.
-- %
-- % Commutativity, associativity, and Huntington's axiom 
-- % axiomatize Boolean algebra.

module! ROBBINS (E :: TRIV)
{
  op _+_ : Elt Elt -> Elt { r-assoc }
  op n : Elt -> Elt
  vars x y z : Elt
  eq x + y = y + x .
  eq (x + y) + z = x + (y + z) .
  eq  n(n(x + y) + n(x + n(y))) = x . -- Robbins axiom
}

option reset

open ROBBINS .
protecting (FOPL-CLAUSE)

ops A B C : -> Elt .

** hypothesis---exists a 1
eq x + C = C .

**
goal n(A + n(B)) + n(n(A) + n(B)) = B .

flag(auto,on)
flag(universal-symmetry, on)
flag(back-sub,off)
resolve .
close
** 
eof
**
$Id:
