** translated from examples of OTTER-3.0.5 examples/auto/steam.in

-- %                Schubert's Steamroller
-- % 
-- % Wolves, foxes, birds, caterpillars, and snails are animals,
-- % and there are some of each of them.
-- % 
-- % Also there are some grains, and grains are plants.
-- % 
-- % Every animal either likes to eat all plants or all animals much
-- % smaller than itself that like to eat some plants.
-- % 
-- % Caterpillars and snails are much smaller than birds, which are much
-- % smaller than foxes, which are in turn much smaller than wolves.
-- % 
-- % Wolves do not like to eat foxes or grains, while birds like to eat
-- % caterpillars but not snails.
-- % 
-- % Caterpillars and snails like to eat some plants.
-- % 
-- % Prove there is an animal that likes to eat a grain-eating animal.
-- %

module! STEAM
{ 
  protecting (FOPL-CLAUSE)
  [ E ]
  pred Wolf : E
  pred Fox  : E
  pred Bird : E
  pred Caterpillar : E
  pred Snail : E
  pred Grain : E
  pred animal : E
  pred plant  : E
  pred eats : E E
  pred Smaller : E E

  vars u x y z  : E

  ax \A[x]Wolf(x) -> animal(x).
  ax \A[x]Fox(x) -> animal(x).
  ax \A[x]Bird(x) -> animal(x).
  ax \A[x]Caterpillar(x) -> animal(x).
  ax \A[x]Snail(x) -> animal(x).
  ax \A[x]Grain(x) -> plant(x).

  ax \E[x]Wolf(x).
  ax \E[x]Fox(x).
  ax \E[x]Bird(x).
  ax \E[x]Caterpillar(x).
  ax \E[x]Snail(x).
  ax \E[x]Grain(x).

  **  All animals either eat all plants or eat all smaller animals
  **  that eat some plants.  
  ax \A[x] (animal(x) -> (\A[y] plant(y) -> eats(x,y))
	    |  (\A[z] animal(z) & Smaller(z,x) &
		  (\E[u] plant(u) & eats(z,u))
		-> eats(x,z))).
  ax \A[x,y]Caterpillar(x) & Bird(y) -> Smaller(x,y) .
  ax \A[x,y]Snail(x) & Bird(y) -> Smaller(x,y).
  ax \A[x,y]Bird(x) & Fox(y) -> Smaller(x,y).
  ax \A[x,y]Fox(x) & Wolf(y) -> Smaller(x,y).
  ax \A[x,y]Bird(x) & Caterpillar(y) -> eats(x,y).

  ax \A[x]Caterpillar(x) -> (\E[y] plant(y) & eats(x,y)).
  ax \A[x]Snail(x)       -> (\E[y] plant(y) & eats(x,y)).

  ax \A[x,y]Wolf(x) & Fox(y) -> ~(eats(x,y)).
  ax \A[x,y]Wolf(x) & Grain(y) -> ~(eats(x,y)).
  ax \A[x,y]Bird(x) & Snail(y) -> ~(eats(x,y)).

}

open STEAM .
"there is an animal that eats an animal that eats all grains".
goal \E[x,y] ~($Ans(eats(x,y))) &
             animal(x) &
             animal(y) &
             eats(x,y) &
	     (\A[z] Grain(z) -> eats(y,z)) .

option reset
flag (auto,on)
resolve .
close
**
eof
**
$Id:
