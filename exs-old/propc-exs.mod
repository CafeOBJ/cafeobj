** -*- Mode:CafeOBJ -*-
**> Some example reductions in PROPC.

select PROPC
--> a or not a
reduce in PROPC : a or not a .
--> a or b <-> b or a 
reduce a or b <-> b or a .
-->  a -> (b -> a) .
reduce a -> (b -> a) .
-->  a -> b <-> not b -> not a .
reduce a -> b <-> not b -> not a .
-->  not(a or b) <-> not a and not b .
reduce not(a or b) <-> not a and not b .
--> c or c and d <-> c .
reduce c or c and d <-> c .
-->  a <-> a <-> a <-> a .
reduce a <-> a <-> a <-> a .
--> a -> b and c <-> (a -> b) and (a -> c).
reduce a -> b and c <-> (a -> b) and (a -> c) .
--> a <-> not b 
**> should be: a xor b
reduce a <-> not b . 
--> a and b xor c xor b and a . 
**> should be: c
reduce a and b xor c xor b and a . 
--> a -> (b -> not a).  
**> should be: true xor (b and a)
reduce a -> (b -> not a).  
--> a and not a 
**> should be: false
reduce a and not a .
--> a <-> a <-> a 
**> should be: a
reduce a <-> a <-> a .
--
eof
--
$Id: propc-exs.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
