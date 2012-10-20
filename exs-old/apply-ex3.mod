** -*- Mode:CafeOBJ -*-
--
"
From `Introducing OBJ'

similar to apply-ex2.mod, but simplified assuming associativity of the
group multiplications as an attribute.
"

module GROUPA {
  [ Elt ]
  op _*_ : Elt Elt -> Elt { assoc }
  op e : -> Elt
  op _-1 : Elt -> Elt { prec: 2 }
  var A : Elt
  eq [lid] : e * A = A .
  eq [linv] : A -1 * A = e .
}

**> open GROUPA
open GROUPA .
--> show .
show .
--> op a : -> Elt .
op a : -> Elt .
**> first, prove the right inverse law:
--> start a * a -1 .
start a * a -1 .
--> apply -.lid at top
apply -.lid at top
--> should be : e * a * a -1
--> apply -.linv with A = (a -1) within top
apply -.linv with A = (a -1) within top
--> should be : a -1 -1 * a -1 * a * a -1
--> choose [ 2 .. 3 ] .
choose [ 2 .. 3 ] .
--> show context
show context
--> apply .linv at subterm
apply .linv at subterm
--> should be : a -1 -1 * e * a -1
--> apply reduction at top
apply reduction at top
--> should be : e
**> add the proven equation:
--> eq [rinv] : XX:Elt * XX -1 = e .
eq [rinv] : XX:Elt * XX -1 = e .
--> show .
show .
**> second prove the right identity law:
--> start a * e .
start a * e .
--> apply -.linv with A = a within top
apply -.linv with A = a within top
--> should be : a * a -1 * a
--> choose [ 1 .. 2 ] .
choose [ 1 .. 2 ] .
--> sh context
show context
--> apply .rinv at subterm
apply .rinv at subterm
--> should be : e * a
--> apply reduction at top
apply red at top
--> should be : a
**> add the proven equation:
--> eq [rid]: XX:Elt * e = XX .
eq [rid]: XX:Elt * e = XX .
**> close
close

eof
**
$Id: apply-ex3.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
