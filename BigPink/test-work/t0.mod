** test formula translation
open BOOL .
protecting (FOPL-CLAUSE)
ops P Q R : -> Bool .
let t1 = (P | Q) & (P | Q | R) .
let t2 = (P & Q) | (P & Q & R) .


**
eof
**
$Id:
