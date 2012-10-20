module! NAT' 
{
  signature {
    [ Zero < Nat ]
    op 0 : -> Zero {strat: (0)}
    op s : Nat -> Nat {strat: (1 0)}
    op _+_ : Nat Nat -> Nat {strat: (1 2 0)}
    op _-_ : Nat Nat -> Nat {strat: (1 2 0)}
    op _*_ : Nat Nat -> Nat {strat: (1 2 0)}
    op _/_ : Nat Nat -> Nat {strat: (1 2 0)}
    op _%_ : Nat Nat -> Nat {strat: (1 2 0)}
    op _===_ : Nat Nat -> Bool {strat: (1 2 0)}
    op _!=_ : Nat Nat -> Bool {strat: (1 2 0)}
    op _<_ : Nat Nat -> Bool {strat: (1 2 0)}
    op _>_ : Nat Nat -> Bool {strat: (1 2 0)}
    op _<=_ : Nat Nat -> Bool {strat: (1 2 0)}
    op _>=_ : Nat Nat -> Bool {strat: (1 2 0)}
    op gcd : Nat Nat -> Nat {strat: (1 2 0)}
    op fact : Nat -> Nat {strat: (1 0)}
    op power : Nat Nat -> Nat {strat: (1 2 0)}
  }
  axioms{
   vars X Y : Nat
    -- +
    eq X + 0 = X .
    eq X + s(Y) = s(X + Y) .
    -- -
    eq X - 0 = X .
    eq s(X) - s(Y) = X - Y .
    -- *
    eq X * 0 = 0 .
    eq 0 * X = 0 .
    eq X * s(Y) = X + (X * Y) .
    -- /
    cq X / Y = 0 if (X < Y) .
    ceq X / Y = s((X - Y) / Y) if not (X < Y) .
    -- %
    ceq X % Y = X if X < Y .
    ceq X % Y = (X - Y) % Y if not (X < Y) .
    -- ===
    eq X === X = true .
    eq 0 === s(X) = false .
    eq s(X) === 0 = false .
    eq s(X) === s(Y) = X === Y .
    -- != 
    eq X != Y = not (X === Y) .
    -- <
    eq X < 0 = false .
    eq 0 < s(X) = true .
    eq s(X) < s(Y) = X < Y .
    -- >
    eq 0 > X = false .
    eq s(X) > 0 = true .
    eq s(X) > s(Y) = X > Y .
    -- <=
    eq X <= Y = not (X > Y) .
    -- >=
    eq X >= Y = not (X < Y) .
    -- gcd
    eq gcd(X, X) = X .
    ceq gcd(X, Y) = gcd(X - Y, Y) if X > Y .
    ceq gcd(X, Y) = gcd(X, Y - X) if X < Y .
    -- fact
    eq fact(0) = s(0) .
    eq fact(s(X)) = s(X) * fact(X) .
    -- power
    eq power(X, 0) = s(0) .
    eq power(X, s(Y)) = X * power(X, Y) .
  }
}

module! FROMDEC {
  extending (NAT')
  op 1 : -> Nat {strat: (0)}
  op 2 : -> Nat {strat: (0)}
  op 3 : -> Nat {strat: (0)}
  op 4 : -> Nat {strat: (0)}
  op 5 : -> Nat {strat: (0)}
  op 6 : -> Nat {strat: (0)}
  op 7 : -> Nat {strat: (0)}
  op 8 : -> Nat {strat: (0)}
  op 9 : -> Nat {strat: (0)}
  op 10 : -> Nat {strat: (0)}
  op num : Nat -> Nat {strat: (1 0)}
  op num : Nat Nat -> Nat {strat: (1 2 0)}
  op num : Nat Nat Nat -> Nat {strat: (1 2 3 0)}

  eq 1 = s(0) .
  eq 2 = s(s(0)) .
  eq 3 = s(s(s(0))) .
  eq 4 = s(s(s(s(0)))) .
  eq 5 = s(s(s(s(s(0))))) .
  eq 6 = s(s(s(s(s(s(0)))))) .
  eq 7 = s(s(s(s(s(s(s(0))))))) .
  eq 8 = s(s(s(s(s(s(s(s(0)))))))) .
  eq 9 = s(s(s(s(s(s(s(s(s(0))))))))) .
  eq 10 = s(s(s(s(s(s(s(s(s(s(0)))))))))) .
  
  vars X Y Z : Nat
  eq num(X) = X .
  eq num(X, Y) = (X * 10) + Y .
  eq num(X, Y, Z) = (((X * 10) + Y) * 10) + Z .
}

module! TODEC {
  extending (FROMDEC)

  op to-dec : Nat -> Nat {strat: (1 0)}
  op u10 : Nat Nat -> Nat {strat: (1 0)}
  op dec : Nat -> Nat {strat: (1 0)}
  op (.) : -> Nat {strat: (0)}
  op 0. : Nat -> Nat {strat: (1)}
  op 1. : Nat -> Nat {strat: (1)}
  op 2. : Nat -> Nat {strat: (1)}
  op 3. : Nat -> Nat {strat: (1)}
  op 4. : Nat -> Nat {strat: (1)}
  op 5. : Nat -> Nat {strat: (1)}
  op 6. : Nat -> Nat {strat: (1)}
  op 7. : Nat -> Nat {strat: (1)}
  op 8. : Nat -> Nat {strat: (1)}
  op 9. : Nat -> Nat {strat: (1)}

  vars X Y : Nat
    
  eq to-dec(0) = 0.(.) .
  eq to-dec(s(X)) = to-dec(u10(s(X), 0)) .
  eq to-dec(u10(X, Y)) = dec(u10(X, Y)) .
  ceq u10(X, Y) = u10(X / 10, u10(X % 10, Y)) if X >= 10 .
  eq dec(0) = (.) .
  eq dec(u10(0, X)) = 0.(dec(X)) .
  eq dec(u10(s(0), X)) = 1.(dec(X)) .
  eq dec(u10(s(s(0)), X)) = 2.(dec(X)) .
  eq dec(u10(s(s(s(0))), X)) = 3.(dec(X)) .
  eq dec(u10(s(s(s(s(0)))), X)) = 4.(dec(X)) .
  eq dec(u10(s(s(s(s(s(0))))), X)) = 5.(dec(X)) .
  eq dec(u10(s(s(s(s(s(s(0)))))), X)) = 6.(dec(X)) .
  eq dec(u10(s(s(s(s(s(s(s(0))))))), X)) = 7.(dec(X)) .
  eq dec(u10(s(s(s(s(s(s(s(s(0)))))))), X)) = 8.(dec(X)) .
  eq dec(u10(s(s(s(s(s(s(s(s(s(0))))))))), X)) = 9.(dec(X)) .

}

eof
