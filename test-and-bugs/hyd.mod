require simple-int

module HYDRA {
  protecting (INT)
  signature {
    [ List ]
    op nil : -> List
    op [__] : Nat List -> List
    op hydra : Nat List -> Nat {memo}
    op appcp : Nat Nat List -> List {memo}
  }
  axioms {
    vars x N : Nat
    var L : List
    eq hydra(x, nil) = x .
    ceq hydra(x, [N L]) = hydra (x + 1, appcp(x + 1, N - 1, L)) if N > 0 .
    eq hydra(x, [0 L]) = hydra(x + 1, L) .
    ceq appcp(x, N, L) = appcp(x - 1, N, [ N L ]) if x > 0 .
    eq appcp(0, N, L) = L .
  }
}

-- reduce in HYDRA : hydra(0, [ 4 nil ]) .

module HYDRA2 {
  protecting (SIMPLE-INT)
  signature {
    [ List ]
    op nil : -> List
    op [__] : Nat List -> List
    op hydra : Nat List -> Nat { strategy: (2 0 1 2 0) memo}
    op appcp : Nat Nat List -> List {memo}
  }
  axioms {
    vars x N : Nat
    var L : List
    eq hydra(x, nil) = x .
    eq hydra(x, [succ(N) L]) = hydra (succ(x), appcp(succ(x), N, L)) .
    eq hydra(x, [0 L]) = hydra(succ(x), L) .
    eq appcp(succ(x), N, L) = appcp(x, N, [ N L ]) .
    eq appcp(0, N, L) = L .
  }
}

-- reduce in HYDRA2

-- reduce hydra(0, [ succ(succ(succ(succ(0)))) nil ] ) .
