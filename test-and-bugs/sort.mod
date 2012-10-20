  module* TOSET {
    [ Elt ]
    op _<_ : Elt Elt -> Bool
    vars E1 E2 E3 : Elt
    eq E1 < E1 = false .
    cq E1 < E3 = true if (E1 < E2) and (E2 < E3) .
    cq (E1 < E2) or (E2 < E1) = true if E1 =/= E2 .
  }

  module! LIST (X :: TRIV) {
    protecting (NAT)
    [ Elt < NeList < List ]
    op nil : -> List
    op __ : List List -> List { assoc id: nil }
    op __ : NeList List -> NeList { r-assoc }
    op head : NeList -> Elt
    op tail : NeList -> List
    op empty? : List -> Bool
    op length : List -> Nat
    op del1 : Elt List -> List
    op _in_ : Elt List -> Bool
    op perm : List List -> Bool   
    -- ------------------------------
    vars X Y Z W : Elt
    vars L K : List
    eq head(X L) = X .
    eq tail(X L) = L .
    eq empty?(L) = L == nil .
    eq length(nil) = 0 .
    eq length(X L) = length(L) + 1 .
    eq del1(X, nil) = nil .
    eq del1(X, X) = nil .
    cq del1(X, Y) = Y if X =/= Y .
    eq del1(X, X Y L) = Y L .
    cq del1(X, Y Z L) = Y del1(X, Z L) if X =/= Y .
    eq X in nil = false .
    eq X in X = true .
    cq X in Y = false if X =/= Y .
    eq X in (X Y L) = true .
    cq X in (Y Z L) = X in (Z L) if X =/= Y .
    eq perm(nil, nil) = true .
    eq perm(nil, X) = false .
    eq perm(nil, X Y L) = false .
    eq perm(X, nil) = false .
    eq perm(X, X) = true .
    cq perm(X, Y) = false if X =/= Y .
    eq perm(X, Y Z L) = false .
    eq perm(X Y L, nil) = false .
    eq perm(X Y L, Z) = false .
    cq perm(X Y L, Z W K) = perm(Y L, del1(X, Z W K)) if X in (Z W K) .
    cq perm(X Y L, Z W K) = false if not (X in (Z W K)) .
  }

  module! SORTED-LIST (X :: TOSET) {
    protecting (LIST(X <= view to X { sort Elt -> Elt }))
    op sorted : List -> Bool
    vars X Y : Elt
    var L : List
    eq sorted(nil) = true .
    eq sorted(X) = true .
    eq sorted(X Y L) = (X < Y or X == Y) and sorted(Y L) .
  }

  module QSORT (X :: TOSET) {
    protecting (SORTED-LIST(X <= view to X { sort Elt -> Elt }))
    ops smaller larger : Elt List -> List { strat: (1 2 0) }
    op qsort : List -> List
    -- -----------------------------------
    vars X Y : Elt
    var L : List
    eq smaller(X, nil) = nil .
    cq smaller(X, Y L) = Y smaller(X, L) if Y < X .
    cq smaller(X, Y L) = smaller(X, L) if not (Y < X) .
    eq larger(X, nil) = nil .
    cq larger(X, Y L) = Y larger(X, L) if not (Y < X) .
    cq larger(X, Y L) = larger(X, L) if Y < X .
    eq qsort(nil) = nil .
    eq qsort(X L) = qsort(smaller(X,L)) X qsort(larger(X,L)) .
  }

  module! YOUR-NAT {
    [ Nat ]
    op 0 : -> Nat
    op s : Nat -> Nat
    op _<_ : Nat Nat -> Bool
    vars N N' : Nat
    eq N < 0 = false .
    eq 0 < s(N) = true .
    eq s(N) < s(N') = N < N' .
  }
   
  view NAT-AS-TOSET from TOSET to YOUR-NAT {
    sort Elt -> Nat
    op _<_ -> _<_
  }

  module! NAT-QSORT {
    protecting (QSORT(NAT-AS-TOSET))
  }

