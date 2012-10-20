module TEST1-3
{
  [ Elt ]
  pred Shaves : Elt Elt
  op Barber : -> Elt
}
open TEST1-3 .
protecting (FOPL-CLAUSE)
ax Shaves(X:Elt, X) | Shaves(Barber, X) .
ax ~(Shaves(Barber, Y:Elt) & Shaves(Y,Y)) .
goal Shaves(Barber, Barber) .
-- goal ~ Shaves(Barber, Barber) .

option reset
flag(auto,on)
resolve .

close

**
eof
**
$Id
