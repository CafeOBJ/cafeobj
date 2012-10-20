** -*- Mode:CafeOBJ -*-
-- prove commutativity of _+_ on natural number.

require tiny-nat ./tiny-nat

module! VARS {
  extending (TINY-NAT)
  ops m n : -> Nat
}

**> first lemma0: 0 + n = n, by induction on n
**> base for lemma0, n=0
select VARS
reduce 0 + 0 == 0 .
**> induction step
module! STEP0 {
  using(VARS)
  eq 0 + n = n .
}
select STEP0
reduce 0 + s n == s n .
** thus we can assert
module! LEMMA0 {
  protecting (TINY-NAT)
  vars N : Nat 
  eq 0 + N = N .
}
show LEMMA0

**> show lemma1: s m + n = s(m + n), again by induction on n
**> base for lemma1, n=0
select VARS
reduce s m + 0 == s(m + 0) .
**> induction step
module! STEP1 {
  using (VARS)
  eq s m + n = s(m + n) .
}
select STEP1
reduce s m + s n == s(m + s n) .
** thus we can assert
module! LEMMA1 {
  protecting (TINY-NAT)
  vars M N : Nat
  eq s M + N = s(M + N).
}
show  LEMMA1
**> show m + n = n + m, again by induction on n
**> base case, n=0
select VARS + LEMMA0
reduce m + 0 == 0 + m .
**> induction step
--> open VARS + LEMMA1
select VARS + LEMMA1
open .
reduce m + s n == s n + m .
**> close
close
eof
**
$Id: comm-add.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
