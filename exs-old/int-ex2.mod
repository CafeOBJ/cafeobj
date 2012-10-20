--                                   -*- Mode:CafeOBJ -*- 

module! INT-EX2 {
  signature {
    [ Int Nat, Nat < Int ]
    ops 0 1 2 : -> Nat 
    op s_ : Nat -> Nat {prec: 1}
    op s_ : Int -> Int {prec: 1}
    op p_ : Int -> Int {prec: 1}
    op + : Nat Nat -> Nat {prec: 3}
    op + : Int Int -> Int {prec: 3}
    op * : Nat Nat -> Nat {prec: 2}
    op * : Int Int -> Int {prec: 2}
    op - : Int Int -> Int {prec: 4 strat (0 1 2)}
    op - : Int -> Int {prec: 1}
  }
  axioms {
    vars I J K : Int 
    var N : Nat 
    -- -------------------------------
    eq 1 = s 0 .
    eq 2 = s 1 .
    eq s p I = I .
    eq p s I = I .
    eq +(I, 0) = I .
    eq +(I,s J) = s(+(I,J)) .
    eq +(I,p J) = p(+(I,J)) .
    eq *(I,0) = 0 .
    eq *(I,s J) = +(*(I,J),I) .
    eq *(I,p J) = -(*(I,J),I) .
    eq *(I,+(J,K)) = +(*(I,J),*(I,K)) .
    eq -(0) = 0 .  
    eq -(-(I)) = I .
    eq -(s I) = p(-(I)) .
    eq -(p I) = s(-(I)) .
    eq -(I,J) = +(I, -(J)) .
    eq +(I,-(I)) = 0 .
    eq -(+(I,J)) = -(-(I),J) .
    eq *(I,-(J)) = -(*(I,J)) .
  }
}

module! INT-COMP2 {
  protecting (INT-EX2)
  op fact : Nat -> Nat
  vars N : Nat
  eq fact(0) = s(0) .
  eq fact(s N) = *(s N, fact(N)) .
}

--
eof
**
$Id: int-ex2.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $

