module SIMPLE-NAT {
  signature {
    [ Zero NzNat < Nat ]
    op 0  : -> Zero
    op s : Nat -> NzNat 
    op _+_ : Nat Nat -> Nat
  }
  axioms {
    vars N N' : Nat
    eq 0 + N = N .
    eq s(N) + N' = s(N + N') .
  }  
}

provide Msimple-nat

eof

** $Id: Msimple-nat.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
