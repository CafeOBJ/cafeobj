** OK
module TEST1-2
{
  [ Elt ]
  pred P : Elt Elt
  pred Q : Elt
  pred R : Elt
  op f : Elt -> Elt
}
open TEST1-2 .
protecting (FOPL-CLAUSE)
op a : -> Elt .
let ax1 = \A[X:Elt] P(X, a) | Q(X) .
let ax2 = \A[X:Elt] P(f(X),X) -> R(X) .

ax ax1 .
ax ax2 .
-- let goal = ~(Q(f(a)) | R(a)) .
ax [goal]: ~(Q(f(a)) | R(a)) .

option reset
flag(neg-hyper-res,on)
flag(factor,on)
flag(unit-deletion,on)
-- goal goal .
db reset
sos = {goal}
list sos
list usable
resolve .
close
--

eof

**
$Id
