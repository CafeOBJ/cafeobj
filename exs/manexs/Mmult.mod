require Msimple-nat

module MULT {
  protecting (SIMPLE-NAT)
  op _*_ : Nat Nat -> Nat
  vars N M : Nat
  eq 0 * N = 0 .
  eq s(N) * M = M + (N * M) .
}

provide Mmult
eof
** -----------------
set step on
select MULT
reduce s(s(0)) * s(s(s(0))) .

** $Id: Mmult.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
