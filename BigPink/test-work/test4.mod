** paramodulation test
** works
** 
module TEST4
{
  [ Elt ]
  op f : Elt Elt -> Elt
  op g : Elt -> Elt
  op h : Elt Elt -> Elt
  op e : -> Elt
  ops a b : -> Elt
  vars X Y Z : Elt
  eq f(e,X) = X .
  eq f(g(X), X) = e .
  eq f(f(X,Y), Z) = f(X,f(Y,X)) .
  eq h(X,Y) = f(X, f(Y,f(g(X), g(Y)))) .
  eq f(X,f(X,X)) = e .
}

open TEST4 .
protecting (FOPL-CLAUSE)
goal h(h(a,b),b) = e .
option reset
flag(auto,on)
resolve .
close
**
eof
**
$Id:
