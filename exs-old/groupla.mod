** -*- Mode:CafeOBJ -*-
** an example of proof in GROUP theory
-- uses associativity of _*_

module* GROUPLA {
  [ Elt ]
  op _*_ : Elt Elt -> Elt {assoc}
  op e : -> Elt 
  op _-1 : Elt -> Elt {prec: 2}
  var A : Elt 
  eq [lid]: e * A = A .
  eq [linv]: A -1 * A = e .
}

open GROUPLA
op a : -> Elt .

** first, prove the right inverse law:
start a * a -1 .
apply -.lid at term .
  **> should be: e * a * a -1
apply -.linv with A = (a -1) within term .
  **> should be: a -1 -1 * a -1 * a * a -1
apply .linv at [2 .. 3] .
  **> should be: a -1 -1 * e * a -1
apply reduction at term .
  **> should be: e

** add the proven equation:
 eq [rinv]: A * A -1 = e .

** second prove the right identity law:
start a * e .
apply -.linv with A = a within term .
  **> should be: a * a -1 * a
apply .rinv at [1 .. 2] .
  **> should be: e * a
apply reduction at term .
  **> should be: a

** add the proven equation:
 eq [rid]: A * e = A .
close
--
eof
**
$Id: groupla.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
