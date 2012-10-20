** -*- Mode:CafeOBJ -*-
-- prove associativity of _+_ on natural number.
--

require tiny-nat ./tiny-nat

module! VARS {
  extending (TINY-NAT)
  ops l m n : -> Nat 
}

--> base case, n=0: l+(m+0)=(l+m)+0
reduce in VARS : l + (m + 0) == (l + m) + 0 .

--> induction step
module! STEP {
  using (VARS)
  eq l + (m + n) = (l + m) + n .
}

--> l + (m + s n) == (l + m) + s n .
reduce in STEP : l + (m + s n) == (l + m) + s n .

-- thus we can assert
module! ASSOC {
  protecting (TINY-NAT)
  vars L M N : Nat 
  eq L + (M + N) = (L + M) + N .
}

show ASSOC 
--
eof
**
$Id: assoc-add.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
