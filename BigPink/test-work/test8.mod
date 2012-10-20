** 
** subset relation
** works
module TEST8
{
  protecting (FOPL-CLAUSE)
  [E]
  pred _<=_ : E E
  ax \A[X:E,Y:E] X <= Y <-> (\A[W:E] W <= X -> W <= Y) .
}

**> set sos by hand
open TEST8 .
let goal = ~(\A[X:E,Y:E,Z:E] X <= Y & Y <= Z -> X <= Z ).
-- goal \A[X:E,Y:E,Z:E] X <= Y & Y <= Z -> X <= Z .
option reset
flag(hyper-res,on)
param(max-proofs,1)
db reset
sos = { goal }
list sos
resolve .
close

**> automatic mode
open TEST8 .
goal \A[X:E,Y:E,Z:E] X <= Y & Y <= Z -> X <= Z .
option reset
flag(auto,on)
resolve .
close
**
eof
**
$Id:
