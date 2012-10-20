** -*- Mode:CafeOBJ -*-

require simple-nat ./simple-nat

module! GCD {
 protecting (SIMPLE-NAT)
 signature {
   op _-_ : Nat Nat -> Nat
   op _<_ : Nat Nat -> Bool
   op gcd : Nat Nat -> Nat
 }
 axioms {
   vars N M : Nat
   -- -----------------------------
   eq 0 - M = 0 .
   eq N - 0 = N .
   eq succ(N) - succ(M) = N - M .
   eq 0 < succ(N) = true .
   eq N < 0 = false .
   eq succ(N) < succ(M) = N < M .
   ceq gcd(N, M) = gcd(M,N) if N < M .
   eq gcd(N,0) = N .
   ceq gcd(succ(N), succ(M)) = gcd(succ(N) - succ(M), succ(M)) if not(N < M) .
 }
}

eof
**
$Id: gcd2.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
