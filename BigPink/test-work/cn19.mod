** tlanslated from example of OTTER3.05 examples/auto/cn19.in
-- The sentential calculus (CN).
--
-- {CN1, CN2, CN3} (Lukasiewicz), along with condensed detachment,
-- axiomatizes the sentential calculus (the classical propositional calculus).

module CN19 (E :: TRIV)
{
  protecting (FOPL-CLAUSE)
  pred P : Elt
  op i : Elt Elt -> Elt
  op n : Elt -> Elt
  vars x y z : Elt
  ax P(i(x,y)) & P(x) -> P(y) .
  ** TODO support label
  -- ax [CN1]: P(i(i(x,y),i(i(y,z),i(x,z)))) .
  -- ax [CN2]: P(i(i(n(x),x),x)) .
  -- ax [CN3]: P(i(x,i(n(x),y))) .
  ax P(i(i(x,y),i(i(y,z),i(x,z)))) .
  ax P(i(i(n(x),x),x)) .
  ax P(i(x,i(n(x),y))) .
}

open CN19 .
-- db reset
option reset
flag(auto,on)
flag(back-unit-deletion,off)
flag(randomize-sos,off)
flag(control-memory,off)
-- flag(print-back-demod,on)
-- flag(auto2,on)
-- flag(very-verbose,on)
-- flag(debug-hyper-res,on)

ops a b c : -> Elt .
goal P(i(i(i(a,b),c),i(b,c))) .

resolve .
close
eof
--
$Id:
