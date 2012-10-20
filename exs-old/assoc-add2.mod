** -*- Mode:CafeOBJ -*-

-- prove associativity of _+_ on natural number.
-- use `open'.

require tiny-nat ./tiny-nat

open TINY-NAT .
ops l m n : -> Nat .

** base case, n=0: l+(m+0)=(l+m)+0
reduce l + (m + 0) == (l + m) + 0 .

** induction step
eq l + (m + n) = (l + m) + n .
reduce l + (m + s n) == (l + m) + s n .
close

** thus we can assert
module! ASSOC {
  protecting (TINY-NAT)
  eq L:Nat + (M:Nat + N:Nat) = (L + M) + N .
}
--
eof
**
$Id: assoc-add2.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
