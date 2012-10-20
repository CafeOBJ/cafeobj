** -*- Mode:CafeOBJ -*-
-- example of non sort decreasing BUT compatible module.
--

module  COMPAT1 {
 [ A < B ]
 op a : -> A
 op b : -> B
 op f : A -> A
 op f : B -> B
 eq a = b .
 eq f(X:A) = X .
}

--
eof
**
$Id: non-compat.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
--
