** works
module TEST5
{
}

open TEST5 .
protecting (FOPL-CLAUSE)

ops P Q R : -> FoplSentence .
goal (P | Q) & (P | R) -> P | (Q & R) .

option reset
flag(auto,on)
resolve .
close
**
eof
**
$Id
