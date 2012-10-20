** -*- Mode:CafeOBJ -*-
--
module! NAT-EX {
  [ Nat ]
  op 0 : -> Nat {constr}
  op s_ : Nat -> Nat {constr prec: 1}
  op _+_ : Nat Nat -> Nat {assoc comm prec: 3}
  op _*_ : Nat Nat -> Nat {prec 2}
  vars M N : Nat 
  eq M + 0 = M .
  eq M + s N = s(M + N).

  eq M * 0 = 0 .
  eq M * s N = M * N + M .
}

provide nat-ex
--
eof
**
$Id: nat-ex.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
--
