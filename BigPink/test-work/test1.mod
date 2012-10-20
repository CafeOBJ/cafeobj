** $Id: test1.mod,v 1.2 2003-11-04 03:11:26 sawada Exp $
** a tiny test
** works
module TEST1-1
{
  [ Elt ]
  pred human : Elt
  pred mortal : Elt
  op Socrates : -> Elt
}

open TEST1-1 .
protecting (FOPL-CLAUSE)
ax \A[X:Elt] human(X) -> mortal(X) .
ax human(Socrates) .
goal mortal(Socrates) .    -- ~mortal(Socrates)
-- let g = ~(mortal(Socrates)) .
-- sos = {g}
-- flag(hyper-res, on)
option reset
flag(auto, on)
flag(very-verbose,on)
param(max-proofs, 1)
resolve .
eof
close
--
eof
--
$Id
