require Msimple-nat

module SUBTRACT {
  protecting (SIMPLE-NAT)
  op _-_ : Nat Nat -> Nat
  vars N N' : Nat
  eq 0 - N = 0 .
  eq N - 0 = N .
  eq s(N) - s(N') = N - N' .
}

provide Msubtract

eof

** $Id: Msubtract.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
