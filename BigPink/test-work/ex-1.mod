** translated from otter 3.0.5 examples/?
-- % 1.  If a lattice with join operation + and meet operation *
-- % satisfies the equation x+(y*z) = (x+y)*(x+z) then it satisfies
-- % the equation x*(y+z) = (x*y)+(x*z). This example illustrates
-- % the sos_queue flag.
-- %
-- % Contributed by John Kalman (kalman@math.auckland.ac.nz)

module EX1
{
  [ E ]
  op _+_ : E E -> E { r-assoc }
  op _*_ : E E -> E { r-assoc }
  ops a b c : -> E 
  vars X Y Z : E 
  eq X = X .
  eq X + Y = Y + X .
  eq X * Y = Y * X .
  eq (X + Y) + Z = X + Y + Z .
  eq (X * Y) * Z = X * Y * Z .
  eq X + (X * Y) = X .
  eq X * (X + Y) = X .
}

option reset
-- flag(kb2,on)
flag(kb,on)
flag(print-kept,off)
flag(print-new-demod,off)
flag(print-back-demod,off)
flag(print-back-sub,on)
** select one from the fllowing 2 options
flag(sos-queue,on)
-- flag(very-verbose,on)
-- flag(trace-demod,off)
-- flag(debug-para-from,on)
-- flag(debug-para-into,on)
-- flag(debug-infer,on)
-- flag(debug-hyper-res,on)
-- param(pick-given-ratio,1)

open EX1 .
protecting (FOPL-CLAUSE)
let a1 = X:E + (Y:E * Z:E) = (X + Y) * (X + Z) .
let a2 = ~(a * (b + c) = (a * b) + (a * c)) .
db reset
sos = { a1 a2 }

resolve .

close
--
-- eof
-- % 3.  If a lattice with join operation + and meet operation *
-- % satisfies the equation (x*y)+(y*z)+(z*x) = (x+y)*(y+z)*(z+x)
-- % then it satisfies both the equations in ex_1. In this example
-- % the inclusion of the two negative unit clauses together, and
-- % the particular choice of the pick_given_ratio parameter,
-- % turn out to be very helpful.
-- %
-- % Contributed by John Kalman (kalman@math.auckland.ac.nz)
-- %
option reset
flag(kb2,on)
flag(print-kept,off)
flag(print-new-demod,off)
flag(print-back-demod,off)
flag(print-back-sub,on)
param(pick-given-ratio,10)
param(max-proofs,2)

open EX1 .
protecting (FOPL-CLAUSE)
ops a b c : -> E .
ops d e f : -> E .
let a1 = (X * Y) + (Y * Z) + (Z * X) = (X + Y) * (Y + Z) * (Z + X) .
let a2 = ~(a + (b * c) = (a + b) * (a + c)) .
let a3 = ~(d * (e + f) = (d * e) + (d * f)) .
lex(a,b,c,_+_,_*_).
db reset
sos = { a1 a2 a3 }

resolve .
close

**
eof
--
$Id
