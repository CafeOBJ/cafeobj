** -*- Mode:CafeOBJ -*-
--> Bubble sort, OBJ3 example tlanslated to CafeOBJ
--
require tiny-list

module* POSET 
     principal-sort Elt
{
  [ Elt ]
  op _<_ : Elt Elt -> Bool 
  vars E1 E2 E3 : Elt 
  eq E1 < E1 = false .
  cq E1 < E3 = true if E1 < E2 and E2 < E3 .
}

module* TOSET 
     principal-sort Elt
{
  using (POSET)
  vars E1 E2 E3 : Elt
  cq E1 < E2 or E2 < E1 = true if E1 =/= E2 .
}

module! BUBBLES(X :: TOSET)
{
  protecting (LIST[X])
  op sorting_ : List -> List 
  op sorted_ : List -> Bool 
  vars L L' L'' : List 
  vars E E' : Elt 
  cq sorting L = L if sorted L .
  cq sorting L E E' L'' = sorting L E' E L'' if E' < E .
  eq sorted nil = true .
  eq sorted E = true .
  cq sorted E E' L = sorted E' L if E < E' or E == E' .
}

view NATD from POSET to NAT {
  vars L1 L2 : Elt,
  op L1 < L2 -> L1 divides L2 and L1 =/= L2 
}

open BUBBLES[NAT] .
reduce sorting(18 5 6 3) .  **> should be: 3 5 6 18
reduce sorting(8 5 4 2) .   **> should be: 2 4 5 8
close
open BUBBLES[NATD] .
reduce  sorting(18 5 6 3) . **> mightnt contain: 3 6 18
reduce sorting(8 5 4 2) .   **> mightnt contain: 2 4 8
close
--
eof
**
$Id: bubbles.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
