** 
** works
**
module TEST6
{
  [ Elt ]
  pred R : Elt Elt
}

open TEST6 .
protecting (FOPL-CLAUSE)
goal (\A[X:Elt] R(X,X)) ->  (\A[X:Elt]\E[Y:Elt] R(X,Y)) .

option reset
flag(auto,on)
resolve .
close
**
eof
**
$Id
