** -*- Mode:CafeOBJ -*-
-- VERY simple natural number.

module! TINY-NAT {
  signature {
   [ Nat ]
    op 0 : -> Nat 
    op s_ : Nat -> Nat {prec: 1}
    op _+_ : Nat Nat -> Nat 
  }
  axioms {
    vars L M N : Nat 
    -- ------------------
    eq M + 0 = M .
    eq M + s N = s(M + N) .
  }
}

provide tiny-nat
--
eof
--
$Id: tiny-nat.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
