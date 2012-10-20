** -*- Mode:CafeOBJ -*-
**> this example is iter.mod translated from OBJ3 example.
-- 
require tiny-list

module* MONOID
     principal-sort M
{
  [ M ]
  op e : -> M 
  op _*_ : M M -> M { assoc id: e }
}

module! ITER (M :: MONOID)
{
  protecting (LIST[M])
  op iter : List -> M 
  var X : M 
  var L : List 
  eq iter(nil) = e .
  eq iter(X) = X .
  eq iter(X L) = X * iter(L) .
}


view NAT* from MONOID to NAT {
  sort M -> Nat,
  op _*_ -> _*_,
  op e -> 1
}

view NAT+ from MONOID to NAT {
  sort M -> Nat,
  op _*_ -> _+_ ,
  op e -> 0 
}

make SIGMA (ITER[NAT+])

reduce in SIGMA : iter(1 2 3 4) .

**> should be: 10

make PI (ITER[NAT*])

reduce in PI : iter(1 2 3 4) .

**> should be: 24

make SIGMA+PI (
  ITER[NAT+] * { op iter -> sigma }
  + 
  ITER[NAT*] * { op iter -> pi }
)

--

eof
**
$Id: iter.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $ 
