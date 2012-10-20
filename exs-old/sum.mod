** -*- Mode:CafeOBJ -*-

require nat-ex ./nat-ex

module! VARS {
  protecting (NAT-EX) 
  ops m n : -> Nat 
}

**> first show two lemmas, 0*n=0 and sm*n=m*n+n
**> base for first lemma
reduce in VARS : 0 * 0 == 0 .
**> induction step for first lemma
module! HYP1 {
  using (VARS)
  eq 0 * n = 0 .
}
reduce in HYP1 : 0 * s n == 0 .
** thus we can assert
module! LEMMA1 {
  protecting (NAT-EX)
  vars N : Nat
  eq 0 * N = 0 .
}

**> base for second lemma
reduce in VARS + LEMMA1 : s n * 0 == n * 0 + 0 .

**> induction step for second lemma
module! HYP2 {
  using (VARS)
  eq s m * n = m * n + n .
}
reduce in HYP2 : s m * s n == (m * s n)+ s n .
-- so we can assert
module! LEMMA2 {
  protecting (NAT-EX)
  vars M N : Nat
  eq s M * N = M * N + N .
}

module! SUM {
  protecting (NAT-EX)
  op sum : Nat -> Nat 
  var N : Nat
  eq sum(0) = 0 .
  eq sum(s N) = s N + sum(N) .
}
**> show sum(n)+sum(n)=n*sn
**> base case
reduce in SUM + LEMMA1 : sum(0) + sum(0) == 0 * s 0 .
**> induction step
module! HYP {
  using (SUM + VARS)
  eq sum(n) + sum(n) = n * s n .
}

reduce in HYP + LEMMA2 : sum(s n) + sum(s n) == s n * s s n .
--
eof
-- 
$Id: sum.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
