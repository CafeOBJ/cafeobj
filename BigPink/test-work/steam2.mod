**
** Many(Order) Sorted Version of STEAM
**

module! STEAM2
{ 
  protecting (FOPL-CLAUSE)
  [ Animal Plant < Life ]
  ops Wolf Fox Bird Caterpillar Snail : -> Animal
  op Grain : -> Plant

  pred eats : Life Life
  pred Smaller : Animal Animal

  vars A1 A2 : Animal
  var P : Plant

  **  All animals either eat all plants or eat all smaller animals
  **  that eat some plants.  
  -- ax \A[A1,A2,P] 
  --     eats(A1,P) | Smaller(A2,A1) & (\E[P] eats(A2,P)) -> eats(A1,A2) .
  -- we can omit leading \A[A1,A2,P] 
  ax eats(A1,P) | Smaller(A2,A1) & (\E[P] eats(A2,P)) -> eats(A1,A2) .

  ** facts
  ax Smaller(Caterpillar, Bird).
  ax Smaller(Snail, Bird).
  ax Smaller(Bird, Fox).
  ax Smaller(Fox, Wolf).
  ax eats(Bird, Caterpillar).

  ax \E[P] eats(Caterpillar,P).
  ax \E[P] eats(Snail,P).

  ax ~(eats(Wolf,Fox)).
  ax ~(eats(Wolf,Grain)).
  ax ~(eats(Bird,Snail)).

}

open STEAM2 .
"there is an animal that eats an animal that eats all grains".
goal \E[A1,A2] eats(A1,A2) & eats(A2,Grain) .

option reset
flag (auto,on)
resolve .
close
**
eof
**
$Id:
