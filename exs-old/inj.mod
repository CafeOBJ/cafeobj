** -*- Mode:CafeOBJ -*-

module* INJ {
  [ A B ]
  op f_ : A -> B 
  op g_ : B -> A 
  var A : A
  vars B B' : B 
  eq [lnv]: g f A = A .
  ceq [inj]: B = B' if g B == g B' .
}

open INJ .
op b : -> B .

start f g b .
apply inj with B' = b at top .
apply red at top .
**> should be: b
close
--
eof
**
$Id: inj.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $

