** translated from OTTER-3.0.5 examples/mv25.in
-- % The (infinitely) Many-Valued sentential calculus (MV).
-- % 
-- % {MV-1,MV-2,MV-3,MV-5} axiomatizes MV.
-- % 

-- set(auto).
-- 
-- list(usable).

-- -P(i(x,y)) | -P(x) | P(y).      % condensed detachment

-- P(i(x,i(y,x))).                 % MV-1
-- P(i(i(x,y),i(i(y,z),i(x,z)))).  % MV-2
-- P(i(i(i(x,y),y),i(i(y,x),x))).  % MV-3
-- P(i(i(n(x),n(y)),i(y,x))).      % MV-5
--
-- % -P(i(n(n(a)),a)) | $ANS(MV_24).
-- -P(i(i(a,b),i(i(c,a),i(c,b)))) | $ANS(MV_25).
-- % -P(i(a,n(n(a)))) | $ANS(MV_29).

-- end_of_list.

module! MV
{
  protecting (FOPL-CLAUSE)
  [Elt]
  pred P : Elt
  op i : Elt Elt -> Elt 
  op n : Elt -> Elt
  vars x y z : Elt
  ax P(i(x,y)) & P(x) -> P(y).
  ax P(i(x,i(y,x))).
  ax P(i(i(x,y),i(i(y,z),i(x,z)))).
  ax P(i(i(i(x,y),y),i(i(y,x),x))).
  ax P(i(i(n(x),n(y)),i(y,x))).
}

open MV .
ops a b c : -> Elt .
option reset
flag(auto,on)

** DOES NOT WORK WITHOUT THE FOLLOWING TWO OPTIONS 
flag(control-memory,off)
param(max-weight,16)
goal P(i(i(a,b),i(i(c,a),i(c,b)))).
resolve .
close
--
eof
**
$Id:
