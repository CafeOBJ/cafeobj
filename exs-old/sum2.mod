** -*- Mode:CafeOBJ -*-

require nat-ex ./nat-ex

open NAT-EX .
ops m n : -> Nat .

** first show two lemmas, 0*n=0 and (sm)*n=(m*n)+n
** base for first lemma
reduce 0 * 0 == 0 .
** induction step for first lemma
eq 0 * n = 0 .
reduce 0 * s n == 0 .
** thus we can assert
eq 0 * N = 0 .

** base for second lemma
reduce (s n)* 0 == (n * 0) + 0 .
** induction step for second lemma
eq (s m) * n = (m * n)+ n .
reduce (s m)*(s n) == (m * s n)+ s n .
** thus
eq (s M)* N = (M * N)+ N .

** now define
op sum : Nat -> Nat .
eq sum(0) = 0 .
eq sum(s N) = (s N)+ sum(N) .

** show sum(n)+sum(n)=n*sn
** base case
reduce sum(0) + sum(0) == 0 * s 0 .
** induction step
eq sum(n) + sum(n) = n * s n .
reduce sum(s n) + sum(s n) == (s n)*(s s n) .
close
--
eof
--
$Id: sum2.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
