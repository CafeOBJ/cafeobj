** -*- Mode:CafeOBJ -*-
--
require set ./set.mod

make INT-SET2 (
  SET[view to INT { sort Elt -> Int }] * { sort Set -> IntSet }
)

-- now CafeOBJ supports `pricipal sort', computing view uses this
-- feature, then the following essentially the same with the following:

make INT-SET (
 SET[INT] * { sort Set -> IntSet }
)

--
eof
--
$Id: set-exs.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
