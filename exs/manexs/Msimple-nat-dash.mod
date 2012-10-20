module SIMPLE-NAT'
     principal-sort Nat
{
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

view V from ONE to SIMPLE-NAT' {
}

view V' from ONE to SIMPLE-NAT' {
  sort Elt -> Nat
}

provide Msimple-nat-dash

eof

** $Id: Msimple-nat-dash.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
