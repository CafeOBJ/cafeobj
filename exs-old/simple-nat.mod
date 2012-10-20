** Mode:CafeOBJ
-- simple natural number
--
module! SIMPLE-NAT
     principal-sort Nat
{
  signature {
    [ Zero NzNat < Nat ]
    op 0 : -> Zero { constr }
    op succ : Nat -> NzNat  { constr }
    op _+_ : Nat Nat -> Nat { associative commutative }
  }
  axioms {
    vars N N' : Nat
    -- ------------------
    eq 0 + N = N .
    eq N + succ(N') = succ(N + N') .
  }
}

provide simple-nat
--
eof
--
$Id: simple-nat.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
