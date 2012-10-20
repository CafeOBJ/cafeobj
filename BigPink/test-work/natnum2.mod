mod! NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  ops 0 : -> NatNum { constr }
  op s : NatNum -> NatNum { constr }
  op _+_ : NatNum NatNum -> NatNum { assoc comm }
  op _*_ : NatNum NatNum -> NatNum { assoc comm }

  vars M N : NatNum
  eq M + 0 = M .
  eq M + s(N) = s(M + N) .
  eq M * 0 = 0 .
  eq M * s(N) = N + (M * N) .

  -- ax ~(s(M) = 0) .
  ax ~(s(M) = M).
  ax M = M .
}

open NATNUM .
eof
option reset
flag(auto,on)
flag(universal-symmetry,off)
flag(very-verbose,on)
-- flag(debug-hyper-res,on)
resolve .
**> aho
eof
**
$Id:
