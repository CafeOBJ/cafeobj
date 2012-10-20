** -*- Mode:CafeOBJ -*-

module! INT-EX {
  signature {
    [ Int Nat, Nat < Int ]
    ops 0 1 2 : -> Nat 
    op s_ : Nat -> Nat {prec: 1}
    op s_ : Int -> Int {prec: 1}
    op p_ : Int -> Int {prec: 1}
    op _+_ : Nat Nat -> Nat {assoc comm prec: 3}
    op _+_ : Int Int -> Int {assoc comm prec: 3}
    op _*_ : Nat Nat -> Nat {assoc comm prec: 2}
    op _*_ : Int Int -> Int {assoc comm prec: 2}
    op _-_ : Int Int -> Int {prec: 4 strat (0 1 2)}
    op -_ : Int -> Int {prec: 1}
    op 2**_ : Nat -> Nat {prec: 1}
  }
  axioms {
    vars I J K : Int 
    var N : Nat 
    -- -------------------------------
    eq 1 = s 0 .
    eq 2 = s 1 .
    eq s p I = I .
    eq p s I = I .
    eq I + 0 = I .
    eq I + s J = s(I + J) .
    eq I + p J = p(I + J) .
    eq I * 0 = 0 .
    eq I * s J = I * J + I .
    eq I * p J = I * J - I .
    eq I * (J + K) = I * J + I * K .
    eq - 0 = 0 .  
    eq - - I = I .
    eq - (s I) = p(- I) .
    eq - (p I) = s(- I) .
    eq I - J = I + (- J) .
    eq I + (- I) = 0 .
    eq -(I + J) = - I - J .
    eq I * (- J) = -(I * J) .
    eq 2** 0 = 1 .
    eq 2** s N = 2** N * 2 .
  }
}

module! INT-COMP {
 protecting (INT-EX)
 op fact : Nat -> Nat
 vars N : Nat
 eq fact(0) = 1 .
 eq fact(s N) = s N * fact(N) .
}

--
eof
**
$Id: int-ex.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $


