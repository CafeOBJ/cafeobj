require Msimple-nat

module* COUNTER {
  protecting (SIMPLE-NAT)
  *[ Counter ]*
  bop read : Counter -> Nat
  bop add : Nat Counter -> Counter
  eq read(add(N:Nat, C:Counter)) = N + read(C) .
}

provide Msimple-nat
--
eof
** $Id: Mcounter.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
