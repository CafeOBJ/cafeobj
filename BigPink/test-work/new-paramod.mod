mod NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  op 0 : -> NatNum
  ops a b c : -> NatNum
  -- ops TT FF : -> Bool
  op s : NatNum -> NatNum
  -- op _<_ : NatNum NatNum -> Bool
  pred _<_ : NatNum NatNum -- { meta-demod }
  vars M N : NatNum
  eq [a0]: (M < s(M)) = true .
  ax [a1]: c = 0 | ~(a < s(a)) | a = b .
  ax [a2]: ~(c = 0) .
  ax [a3]: ~(a = b) .
  ax [a4]: M = M .
}

open NATNUM .
db reset
option reset
flag(process-input,on)
flag(hyper-res,on)
flag(para-from,on)
flag(para-into,on)

-- flag(dynamic-demod-all,on)
-- flag(dynamic-demod,on)
-- flag(back-demod,on)
-- flag(trace-demod,on)
sos = { a0 a1 a2 a3 a4 }
resolve .
**
eof
**
$Id:
