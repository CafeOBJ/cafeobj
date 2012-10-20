** -*- Mode:CafeOBJ -*-
--

"
From `Introducing OBJ'

A standard example in group theory:
prove the right handed versions of the axioms fllow from the left handed varsions.

"

module GROUPL {
 [ Elt ]
 op _*_ : Elt Elt -> Elt 
 op e : -> Elt
 op _-1 : Elt -> Elt { prec: 2 }
 vars A B C : Elt
 eq [lid] : e * A = A .
 eq [lnv] : A -1 * A = e .
 eq [las] : A * (B * C) = (A * B) * C .
}

**> opening GROUPL
open GROUPL .
--> op a : -> Elt .
op a : -> Elt .
**> first, prove the right inverse law:
--> start a * a -1 .
start a * a -1 .
--> sh term tree
show term tree
--> apply -lid at top
apply -lid at top
--> should be : e * (a * a -1)
--> apply -lnv with A = (a -1) within top
apply -lnv with A = (a -1) within top
--> should be : ((a -1) -1 * a -1) * (a * a -1)
--> apply las at top 
apply las at top 
--> should be : ((a -1 -1 * a -1) * a) * a -1
--> apply -las with A = (a -1 -1) within top
apply -las with A = (a -1 -1) within top
--> should be : ((a -1 -1 * (a -1 * a)) * a -1
--> apply lnv within top
apply lnv within top
--> should be : (a -1 -1 * e) * a -1
--> apply -las at top
apply -las at top
--> should be : a -1 -1 * (e * a -1)
--> apply lid within top
apply lid within top
--> should be : a -1 -1 * a -1
--> apply lnv at top
apply lnv at top
--> should be : e
**> we can now add the proven equation.
--> eq [rnv]: (XX:Elt * (XX -1)) = e .
eq [rnv]: (XX:Elt * (XX -1)) = e .
--> show .
show .
**> next, we prove the right identity law:
--> start a * e .
start a * e .
--> apply -lnv with A = a within top
apply -lnv with A = a within top
--> should be : a * (a -1 * a)
--> apply las at top
apply las at top
--> should be : (a * a -1) * a
--> apply rnv within top
apply rnv within top
--> should be : e * a
--> apply lid at top
apply lid at top
--> should be : a
**> we can add the proven equation
--> eq [rid]: XX:Elt * e = XX .
eq [rid]: XX:Elt * e = XX .
--> show .
show .
**> close
close

eof
--
$Id: apply-ex2.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
