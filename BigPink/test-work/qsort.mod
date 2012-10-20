module TUPLE (X :: TRIV)
{
  protecting (FOPL-CLAUSE)
  [ Elt < Tuple ]
  op <> : -> Tuple
  op _#_ : Tuple Tuple -> Tuple
  pred _in_ : Elt Tuple

  vars U V : Elt
  vars X Y Z : Tuple

  -- uniqueness
  ax ~( U # X = <>) .
  ax \A[X,Y,U,V] (U # X = V # Y)
                 -> (U = V & X = Y) .
  -- membership relation
  ax \A[U] ~(U in <>) .
  ax \A[U,V,X] (U in (V # X))
               <-> ((U = V) | U in X) . 
  -- append
  ax \A[X] <> # X = X .
  ax \A[X,Y,Z] (X # Y) # Z = X # (Y # Z) .

  -- some inductive theories
}


module PERM (X :: TRIV)
{
  protecting (TUPLE(X))
  protecting (FOPL-CLAUSE)

  pred perm : Tuple
  
  vars 

  ax perm(<>,<>) .
  ax \A[U,X1,X2,Y1,Y2]
       perm(X1 # < U > # X2, Y1 # < U > # Y2)
       <-> perm(X1 # X2, Y1 # Y2) .
  ax \A[X,Y] perm(X,Y) -> (\A[U] U in X <-> U in Y) .

**
** TODO
**

eof
--
$Id:
