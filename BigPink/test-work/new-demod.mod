mod NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  op 0 : -> NatNum
  ops a b c : -> NatNum
  -- ops TT FF : -> Bool
  op s : NatNum -> NatNum
  -- op _<_ : NatNum NatNum -> Bool
  pred _<_ : NatNum NatNum { meta-demod }
  vars M N : NatNum
  eq (M < s(M)) = true .
  ax c = 0 | ~(a < s(a)) | a = b .
  ax ~(c = 0) .
  ax ~(a = b) .
  ax M = M .
}

open NATNUM .
db reset
option reset
flag(process-input,on)
flag(hyper-res,on)
flag(dynamic-demod-all,on)
flag(dynamic-demod,on)
flag(back-demod,on)
flag(trace-demod,on)
sos = { 1 2 3 4 5 }
resolve .

**
eof
**
$Id:
