** test formula translation
open NAT .
protecting (FOPL-CLAUSE)

ops P Q R : -> Bool .

let g1 = (P | Q) & (~ P | Q | R) & (~ Q | R) & ~ R .


**
eof
**
$Id:
