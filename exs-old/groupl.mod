-- -*- Mode:CafeOBJ -*-
** an example of some proofs in GROUP theory. 
-- 
module* GROUPL {
  [ Elt ]
  op _*_ : Elt Elt -> Elt 
  op e : -> Elt 
  op _-1 : Elt -> Elt {prec: 2}
  vars A B C : Elt 
  eq [lid]: e * A = A .
  eq [lnv]: A -1 * A = e .
  eq [las]: A * (B * C) = (A * B) * C .
}

open GROUPL .
op a : -> Elt .

** first, prove the right inverse law:
start a * a -1 .
 **> [0] (a * a -1)
apply -.lid at term .
 **> [1] e * (a * a -1)
apply -.lnv with A = (a -1) within term .
 **> [2] ((a -1) -1 * a -1) * (a * a -1)
apply .las at term .
 **> [3] ((a -1 -1 * a -1)* a)* a -1
apply -.las with A = (a -1 -1) within term .
 **> [4] ((a -1 -1 * (a -1 * a)) * a -1
apply .lnv within term .
 **> [5] (a -1 -1 * e) * a -1
apply -.las at term .
 **> [6] a -1 -1 * (e * a -1)
apply .lid within term .
 **> [7] a -1 -1 * a -1
apply .lnv at term .
 **> [8] e

** we can now add the proven equation
 eq [rnv]: (A * (A -1)) = e .

** next, we prove the right identity law:
start a * e .
 **> [0] a * e
apply -.lnv with A = a within term .
 **> [1] a *(a -1 * a)
apply .las at term .
 **> [2] (a * a -1)* a
apply .rnv within term .
 **> [3] e * a
apply .lid at term .
 **> [4] a

**> we can add the proven equation
 eq [rid]: A * e = A .

close

--
eof
**
$Id: groupl.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
