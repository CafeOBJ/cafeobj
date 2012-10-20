** -*- Mode:CafeOBJ -*-
-- ==================================================================
-- CHOICE
-- a nondeterministic choice
-- ==================================================================

module! CHOICE { 
 protecting (INT-VALUE)
 op _?_ : Int Int -> Int 
 vars A B : Int
 trans  A ? B => A .
 trans  A ? B => B .
}
--
eof
**
$Id: choise.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
