** -*- Mode: CafeOBJ -*-

**> !!! setting auto context on  !!!
set auto context on

module! NAT-EX {
  [ Nat ]
  op 0 : -> Nat 
  op s_ : Nat -> Nat
  attr s_ {prec 1}
  op _+_ : Nat Nat -> Nat
  attr _+_ {assoc comm prec: 3}
  vars L M N : Nat 
  eq M + 0 = M .
  eq M + s N = s(M + N) .
  op _*_ : Nat Nat -> Nat
  attr _*_ {assoc comm prec: 2}
  eq M * 0 = 0 .
  eq M * s N = M * N + M .
  eq L * (M + N) = L * M + L * N .
  eq M + M + M = 0 .
}
**> base case, x = 0
reduce 0 * 0 * 0 == 0 .
**> induction step
module! VARS {
  extending (NAT-EX)
  op x : -> Nat 
  eq x * x * x = x .
}
reduce s x * s x * s x == s x .

**> !!! setting auto context off !!!
set auto context off

--
eof
**
$Id: mmm.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
--
