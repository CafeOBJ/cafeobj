** -*- Mode:CafeOBJ -*-
**> some views from simple theories translated from OBJ3 example.
--> requries exs/theories.module
 
require theories

view NATG from POSET to NAT {
  op _<_ -> _>_ 
}

view NATLEQ from PREORD to NAT {
  vars L1 L2 : Elt ,
  op L1 <= L2 -> L1 < L2 or L1 == L2 
}

view NATD from POSET to NAT {
  vars L1 L2 : Elt,
  op L1 < L2 -> L1 divides L2 and L1 =/= L2 
}

view NATV from POSET to NAT {
  op _<_ -> _<_
}

view NAT* from MONOID to NAT {
  op _*_ -> _*_,
  op e -> 1 
}

view NAT+ from MONOID to NAT {
  op _*_ -> _+_,
  op e -> 0
}

require tiny-list

view LISTM from MONOID to LIST {
  sort M -> List,
  op _*_ -> __,
  op e -> nil
}
--

provide views
-- 
eof
--
$Id: views.mod,v 1.1.1.1 2003-06-19 08:30:18 sawada Exp $
