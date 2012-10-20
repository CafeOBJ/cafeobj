require Msimple-nat+

module GCD {
  protecting (SIMPLE-NAT+)
  op gcd : Nat Nat -> Nat
  -- --------------------
  vars N M : Nat
  ceq gcd(N, M) = gcd(M, N) if N < M .
  eq gcd(N, 0) = N .
  ceq gcd(s(N), s(M)) = gcd(s(N) - s(M), s(M))
  if not (N < M) .
}

provide Mgcd
--
eof
-- ==============================================
select GCD
reduce gcd(s(s(s(s(s(s(0)))))), s(s(s(s(0))))) .

** $Id: Mgcd.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
