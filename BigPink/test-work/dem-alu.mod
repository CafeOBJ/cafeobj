module DEM-ALU
{
  [ E ]
  ops 0 1 cin a0 b0 a1 b1 a2 b2 a3 b3 : -> E
  op _*_ : E E -> E { r-assoc prec: 41 }
  op _#_ : E E -> E { r-assoc prec: 51 }
  pred p : E
  vars x y z : E
  eq 0 # x = x .
  eq 0 # x = x .
  eq x # 0 = x .
  eq x # x = 0 .
  eq x # x # y = y .
  eq x # y = y # x .
  eq y # x # z = x # y # z .
  eq 0 * x = 0 .
  eq x * 0 = 0 .
  eq 1 * x = x .
  eq x * 1 = x .
  eq x * x = x .
  eq x * x * y = x * y .
  eq x * y = y * x .
  eq y * x * z = x * y * z .
  eq x * (y # z) = (x * y) # (x * z) .
}

option reset
open DEM-ALU  .
protecting (FOPL-CLAUSE)
let sos =
  p((a2 # b2 # 1 # a2 * b2) # (a3 # b3) # 1 # (a0 # b0 # 1 # a0 * b0) * 
     (1 # a0 * b0) * (a1 # b1 # 1 # a1 * b1) * (1 # a1 * b1)*
     (a2 # b2 # 1 # a2 * b2) * (1 # a2 * b2) * (cin # 1) # 
     (a0 # b0 # 1 # a0 * b0) * (1 # a0 * b0) * (a1 # b1 # 1 # a1 * b1) *
     (1 # a1 * b1) * (1 # a2 * b2) * (cin # 1) # 
     (a0 # b0 # 1 # a0 * b0) * (1 # a0 * b0) * (1 # a1 * b1) *
     (a2 # b2 # 1 # a2 * b2)*
     (1 # a2 * b2) * (cin # 1) # (a0 # b0 # 1 # a0 * b0)* 
     (1 # a0 * b0) * (1 # a1 * b1) * (1 # a2 * b2) *
     (cin # 1) # (a0 # b0 # 1 # a0 * b0) * (a1 # b1 # 1 # a1 * b1) *
     (1 # a1 * b1) * (1 # a2 * b2) # (a0 # b0 # 1 # a0 * b0) *
     (a1 # b1 # 1 # a1 * b1) * (1 # a1 * b1) * (a2 # b2 # 1 # a2 * b2)*
     (1 # a2 * b2) # (a0 # b0 # 1 # a0 * b0) * (1 # a1 * b1) *
     (1 # a2 * b2) # (a0 # b0 # 1 # a0 * b0) * (1 # a1 * b1) *
     (a2 # b2 # 1 # a2 * b2) * (1 # a2 * b2) # (1 # a0 * b0) *
     (a1 # b1 # 1 # a1 * b1) * (1 # a1 * b1) * (a2 # b2 # 1 # a2 * b2) * 
     (1 # a2 * b2) * (cin # 1) # (1 # a0 * b0) *
     (a1 # b1 # 1 # a1 * b1) * (1 # a1 * b1) * (1 # a2 * b2) *
     (cin # 1) # (1 # a0 * b0) * (1 # a1 * b1) * (a2 # b2 # 1 # a2 * b2) *
     (1 # a2 * b2) * (cin # 1) # (1 # a0 * b0) * (1 # a1 * b1) *
     (1 # a2 * b2) * (cin # 1) # (a1 # b1 # 1 # a1 * b1) *
     (1 # a2 * b2) # (a1 # b1 # 1 # a1 * b1) *
     (a2 # b2 # 1 # a2 * b2) * (1 # a2 * b2)
     ) .

db reset
sos = { sos }
flag(demod-inf,on)
flag(process-input,on)
-- flag(print-kept,off)
flag(lrpo,on)
param(stats-level,4)
param(demod-limit,-1)
param(max-given, 1)
flag(for-sub,off)
flag(back-sub,off)

resolve .
--
eof
--
$Id:
