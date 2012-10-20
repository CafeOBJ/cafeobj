mod! NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  ops 0 : -> NatNum  { constr }
  op s : NatNum -> NatNum  { constr }
  pred _<_ : NatNum NatNum -- { meta-demod }
  vars M N : NatNum
  -- ax M = 0 | M = s(N) .
  ax ~(s(M) < M) .
  ax ~(s(M) = 0) .
  ax [ax-1]: M < s(M) .
  ax [ax-2]: 0 < s(M) .
  ax [ax-3]: M = 0 | 0 < M .
  -- ax ~(s(M) = M) .
  -- ax ~(0 < M)| ~(M = 0) . 
  -- ax ~(M = N & M < N) .
  -- ax ~(M < N & N < M) .
  -- ax M < N | M = N | N < M .
  ax ~(M < 0) .
  ax M = M .
}

open NATNUM .
option reset
flag(auto,on)
-- flag(universal-symmetry,on)
flag(very-verbose,on)
-- flag(debug-hyper-res,on)
-- resolve .
**> aho
eof

db reset
clause (~(M = s(N)) -> M = 0) | (~(M = 0) -> M = s(N)) .

**
eof
**
$Id:
