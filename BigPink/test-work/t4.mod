module R
{
  protecting (FOPL-CLAUSE)
  [E]
  pred Shaves : E E
  op Barber : -> E
  var x : E
  ax Shaves(x,x) | Shaves(Barber, x) .
  ax Shaves(Barber,x) -> ~(Shaves(x,x)) .
}

open R .
option reset
flag(auto,on)
param(max-proofs,1)
resolve .
close

**
eof
**
$Id:
