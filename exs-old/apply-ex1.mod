** -*- Mode:CafeOBJ -*-
--
"
From `Introducing OBJ'
 some examples of commands apply family commands.
"
module X {
  protecting (QID)
  [ Id < A ]
  op f : A -> A
  var X : A
  cq [:nonexc]: f(X) = f(f(X)) if (f(X) == 'a) .
  eq [:nonexec]: f('b) = 'a .
}

**> first, set X as current
--> select X
select X
--> show .
show .
**> start f ('b).
start f('b) .
--> show apply context
show context
--> apply X.1 at top
apply X.1 at top
--> show apply context
show context
--> show term tree
show term tree
--> apply X.2 within top
apply X.2 within top
--> show term tree
show term tree
--> apply reduction at top
apply red at top
--> show term tree
show term tree

--
eof
**
$Id: apply-ex1.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
