** -*- Mode:CafeOBJ -*-

module! NAT' {
  signature {
    [ Nat ]
    op 0 : -> Nat
    op s_ : Nat -> Nat {prec: 1}
    pred _<_ : Nat Nat
    pred eq : Nat Nat {comm}
  }
  axioms {
    vars N M : Nat
    eq 0 < s N = true .
    eq N < N = false .
    eq s N < 0 = false .
    eq s N < s M = N < M .
    eq eq(N, N) = true .
    eq eq(0, s N) = false .
    eq eq(s N, s M) = eq(N, M) .
  }
}

module! DATA {
  protecting (NAT')
}

module* FLAG {
  protecting (DATA)
  signature {
    ** hidden sort
    *[ Flag ]*
    bops (up_) (dn_) (rev_) : Flag -> Flag 
    bop up?_ : Flag -> Bool
  }
  axioms {
    var F : Flag
    eq up? up F = true .
    eq up? dn F = false .
    eq up? rev F = not up? F .
  }
}


eof
**
$Id: flag.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
