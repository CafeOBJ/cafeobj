**
**
**
module! UTEST
{
  [ Elt ]
  pred P : Elt Elt Elt
  op f : Elt Elt -> Elt
  ops g h : Elt -> Elt
  op a : -> Elt
}

open UTEST .

-- test data

unify f(X:Elt, Y:Elt) to f(Z:Elt, g(Z)) .
close

**
eof
**
$Id
