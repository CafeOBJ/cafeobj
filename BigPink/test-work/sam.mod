** translated from example of OTTER-3.0.5
-- % SAM's Lemma in the P-formulation with hyperresolution
-- % This is not a complete axiomatization, because closure
-- % and function symbols are not included.

module SAM (E :: TRIV)
{
  protecting (FOPL-CLAUSE)
  ops 0 1 : -> Elt
  pred join : Elt Elt Elt
  pred meet : Elt Elt Elt
  vars x y z xy yz xyz x1 y1 z1 : Elt

  ax join(1,x,1).
  ax join(x,1,1).
  ax join(0,x,x).
  ax join(x,0,x).
  ax meet(0,x,0).
  ax meet(x,0,0).
  ax meet(1,x,x).
  ax meet(x,1,x).
  ax meet(x,x,x).
  ax join(x,x,x).
  ax meet(x,y,z) -> meet(y,x,z).
  ax join(x,y,z) -> join(y,x,z).
  ax meet(x,y,z) -> join(x,z,x).
  ax join(x,y,z) -> meet(x,z,x).
  ax meet(x,y,xy) & meet(y,z,yz) & meet(x,yz,xyz) -> meet(xy,z,xyz).
  ax meet(x,y,xy) & meet(y,z,yz) & meet(xy,z,xyz) -> meet(x,yz,xyz).
  ax join(x,y,xy) & join(y,z,yz) & join(x,yz,xyz) -> join(xy,z,xyz).
  ax join(x,y,xy) & join(y,z,yz) & join(xy,z,xyz) -> join(x,yz,xyz).
  ax meet(x,z,x) & join(x,y,x1) & meet(y,z,y1) & meet(z,x1,z1) -> join(x,y1,z1).
  ax meet(x,z,x) & join(x,y,x1) & meet(y,z,y1) & join(x,y1,z1) -> meet(z,x1,z1).

}

open SAM .
ops a b c d e a2 b2 c2 r1 r2 : -> Elt .
goal meet(a2,b2,r1).
ax meet(a,b,c).
ax join(c,r2,1).
ax meet(c,r2,0).
ax meet(r2,b,e).
ax join(a,b,c2).
ax join(c2,r1,1).
ax meet(c2,r1,0).
ax meet(r2,a,d).
ax join(r1,e,a2).
ax join(r1,d,b2).

option reset
flag(auto,on)
flag(back-sub,off)
resolve .
close
**
eof
**
$Id:
