** -*- Mode:CafeOBJ -*-

module! INT-EXT {
 protecting (INT)
 signature {
   -- op gcd : Int Int -> NzNat { strat: (1 2 0) }
   op gcd : Int Int -> NzNat
 }
 axioms {
   vars N N' : Nat
   vars M M' : NzNat
   -- ----------------------------
   ceq N quo M = 0 if N < M .
   ceq N quo M = s((N - M) quo M) if not(N < M) .
   eq (- M) quo M' = - (M quo M') .
   -- ----------------------------
   eq gcd(- M, - M') = gcd(M, M') .
   eq gcd(- M, N) = gcd(M, N) .
   eq gcd(N, - M) = gcd(N, M) .
   eq gcd(0, 0) = s(0) .
   eq gcd(M, 0) = M .
   eq gcd(0, M) = M .
   ceq gcd(M, M') = gcd(M', M) if M < M' .
   ceq gcd(M, M') = gcd(M - M', M') if not(M < M') .
 }
}

module RAT' {
  protecting (INT-EXT)
  [ NzInt < NzRat < Rat, Int < Rat ]
  signature {
    op q : NzInt NzInt -> NzRat
    op q : Int NzInt -> Rat
    op _+_ : Rat Rat -> Rat { associative commutative }
    op _-_ : Rat Rat -> Rat
    op _*_ : Rat Rat -> Rat { associative commutative }
    op _/_ : Rat NzRat -> Rat
    -- -----------------------
    op c : Int -> NzInt
  }
  axioms {
    vars I I' : Int
    vars J J' K : NzInt
    ceq q(I,J) = q(I quo gcd(I,J),c(J quo gcd(I,J)))
      if s(0) < gcd(I,J) .
    eq q(I,s(0)) = I .
    eq q(I,J) + q(I',J') = q(I * J' + I' * J, J * J') .
    eq q(I,J) - q(I',J') = q(I * J' - I' * J, J * J') .
    eq q(I,J) * q(I',J') = q(I * I', J * J') .
    eq q(I,J) / q(K, J') = q(I * J', J * K) .
    eq q(I,J) + I' = q(I + J * I', J) .
    eq q(I,J) - I' = q(I - J * I', J) .
    eq I' - q(I,J) = q(I' * J - I, J) .
    eq q(I,J) * I' = q(I * I', J) .
    eq q(I,J) / K = q(I, J * K) .
    eq I / q(J,J') = q(I * J', J) .
    eq c(J) = J .
  }
}


eof
**
$Id: gcd.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
