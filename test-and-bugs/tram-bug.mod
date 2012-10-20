mod MYNAT {
 [NzNat < Nat]

 op 0 : -> Nat
 op s : Nat -> NzNat
 op _+_ : Nat Nat -> Nat
 op _*_ : Nat Nat -> Nat
 op fact : Nat -> NzNat
 ops 1 2 3 4 5 6 7 8 9 : -> NzNat

 vars N M : Nat

 eq 0 + N = N .
 eq N + 0 = N .
 eq N + s(M) = s(N + M) .

 eq 0 * N = 0 .
 eq N * 0 = 0 .
 eq N * s(M) = N + (N * M) .

 eq fact(0) = s(0) .
 eq fact(s(N)) = s(N) * fact(N) .

 eq 1 = s(0) .
 eq 2 = s(1) .
 eq 3 = s(2) .
 eq 4 = s(3) .
 eq 5 = s(4) .
 eq 6 = s(5) .
 eq 7 = s(6) .
 eq 8 = s(7) .
 eq 9 = s(8) .
}

