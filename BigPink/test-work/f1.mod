**
** need of factoring
**
module T1
{ [E]
  protecting (FOPL-CLAUSE)
  pred P : E
}

option reset
open T1 .
ax P(X:E) | P(Y:E) .
ax ~(P(X:E)) | ~(P(Y:E)) .
flag(auto,on)
resolve .
close
**

** manual version
option reset
open T1 .
let a1 = P(X:E) | P(Y:E) .
ax ~(P(X:E)) | ~(P(Y:E)) .
** we need db reset
db reset
sos = { a1 }
flag(binary-res,on)
flag(unit-deletion,on)
flag(factor,off)
**> this should fail.
resolve .
list usable
close
--
eof
--
$Id:
