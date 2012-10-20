** -*- Mode:CafeOBJ -*-
--

"
From `Introducing OBJ'

Proving that an injective function with a right inverse is an isomorphism.
A good illastration of apply when there are conditinal equations.
"

module INJ {
  [ A B ]
  op f_ : A -> B
  op g_ : B -> A
  var A : A
  vars B B' : B
  eq [lnv]: g f A = A .
  cq [inj]: B = B' if g B == g B' .
}

**> set reduce conditions to "off" for avoiding infinite rewriting step.
--> set reduce conditions off
set reduce conditions off
**> open INJ
open INJ 
--> show .
show .
--> op b : -> B .
op b : -> B .
--> start f g b .
start  f g b .
--> apply .inj with B' = b at top
apply .inj with B' = b at top
--> show context
show context
--> apply red at top
apply red at top
--> should be: b
**> closing
close

eof
**
$Id: apply-ex4.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
