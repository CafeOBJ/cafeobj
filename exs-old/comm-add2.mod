** -*- Mode:CafeOBJ -*-

require tiny-nat ./tiny-nat

open TINY-NAT .
ops m n : -> Nat .

** show lemma0: 0 + n = n, by induction on n
** base for lemma0, n=0
reduce 0 + 0 == 0 .
** induction step
eq 0 + n = n .
reduce 0 + (s n) == s n .
** thus we can assert
eq 0 + N = N .

** show lemma1: (s m) + n = s(m + n), again by induction on n
** base for lemma1, n=0
reduce (s m)+ 0 == s(m + 0) .
** induction step
eq (s m)+ n = s(m + n) .
reduce (s m) + (s n) == s(m + s n) .
** thus we can assert
eq (s M)+ N = s(M + N).

** show m + n = n + m, again by induction on n
** the base case, n=0
reduce m + 0 == 0 + m .
** induction step
eq m + n = n + m .
reduce m + (s n) == (s n) + m .
close
eof
**
$Id: comm-add2.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
