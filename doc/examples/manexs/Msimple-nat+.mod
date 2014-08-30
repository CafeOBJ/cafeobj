require Msimple-nat

module SIMPLE-NAT+ {
  protecting (SIMPLE-NAT)
  op _-_ : Nat Nat -> Nat
  op _<_ : Nat Nat -> Bool
  -- ---------------------
  vars N M : Nat
  eq 0 - M = 0 .
  eq N - 0 = N .
  eq s(N) - s(M) = N - M .
  eq 0 < s(N) = true .
  eq N < 0 = false .
  eq s(N) < s(M) = N < M .
}

provide Msimple-nat+

eof

** $Id: Msimple-nat+.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
