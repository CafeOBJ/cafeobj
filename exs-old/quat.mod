** -*- Mode:CafeOBJ -*-

module! NAT' {
  signature {
    [ Zero NzNat < Nat ]
    op 0  : -> Zero
    op s_ : Nat -> NzNat 
    op p_ : NzNat -> Nat 
    op _+_ : Nat Nat -> Nat {assoc comm}
    op _*_ : Nat Nat -> Nat 
    op _*_ : NzNat NzNat -> NzNat 
    op _>_ : Nat Nat -> Bool 
    op d : Nat Nat -> Nat {comm}
    op quot : Nat NzNat -> Nat 
    op gcd : NzNat NzNat -> NzNat {comm}
  }
  axioms {
    vars N M : Nat vars N' M' : NzNat 
    eq p s N = N .
    eq N + 0 = N .
    eq (s N) + (s M) = s s (N + M) .
    eq N * 0 = 0 .
    eq 0 * N = 0 .
    eq (s N) * (s M) = s (N + (M + (N * M))) .
    eq 0 > M = false .
    eq N' > 0 = true . 
    eq s N > s M = N > M .
    eq d(0,N) = N .
    eq d(s N, s M) = d(N,M) .
    eq quot(N,M') = if ((N > M') or (N == M')) then s quot(d(N,M'),M') 
       else 0 fi .
    eq gcd(N',M') = if N' == M' then N' else (if N' > M' then 
       gcd(d(N',M'),M') else gcd(N',d(N',M')) fi) fi .
  }
}


module! INT' {
  protecting (NAT')
  signature {
    [ Nat < Int, NzNat < NzInt < Int ]
    op -_ : Int -> Int 
    op -_ : NzInt -> NzInt 
    op _+_ : Int Int -> Int {assoc comm}
    op _*_ : Int Int -> Int 
    op _*_ : NzInt NzInt -> NzInt 
    op quot : Int NzInt -> Int 
    op gcd : NzInt NzInt -> NzNat {comm}
  }
  axioms {
    vars I J : Int    vars I' J' : NzInt 
    vars N' M' : NzNat 
    eq - - I = I .
    eq - 0 = 0 .
    eq I + 0 = I .
    eq M' + (- N') = if N' == M' then 0 else 
       (if N' > M' then - d(N',M') else d(N',M') fi) fi .
    eq (- I) + (- J) = - (I + J) .
    eq I * 0 = 0 .
    eq 0 * I = 0 .
    eq I * (- J) = - (I * J) .
    eq (- J) * I = - (I * J) .
    eq quot(0,I') = 0 .
    eq quot(- I',J') = - quot(I',J') .
    eq quot(I',- J') = - quot(I',J') .
    eq gcd(- I',J') = gcd(I',J') .
  }
}

module! RAT' {
  protecting (INT')
  signature {
    [ Int < Rat, NzInt < NzRat < Rat ]
    op _/_ : Rat NzRat -> Rat 
    op _/_ : NzRat NzRat -> NzRat 
    op -_  : Rat -> Rat 
    op -_  : NzRat -> NzRat 
    op _+_ : Rat Rat -> Rat {assoc comm}
    op _*_ : Rat Rat -> Rat 
    op _*_ : NzRat NzRat -> NzRat 
  }
  axioms {
    vars I' J' : NzInt   vars R S : Rat 
    vars R' S' : NzRat 
    eq R / (R' / S') = (R * S') / R' .
    eq (R / R') / S' = R / (R' * S') .
    cq J' / I' = quot(J',gcd(J',I')) / quot(I',gcd(J',I'))
       if gcd(J',I') =/= s 0 .
    eq R / s 0 = R .
    eq 0 / R' = 0 .
    eq R / (- R') = (- R) / R' .
    eq - (R / R') = (- R) / R' .
    eq R + (S / R') = ((R * R') + S) / R' .
    eq R * (S / R') = (R * S) / R' .
    eq (S / R') * R = (R * S) / R' .
  }
}

module! CPX-RAT {
  protecting (RAT')
  signature {
    [ Rat < Cpx,
      NzRat < NzCpx,
      NzImag < NzCpx Imag < Cpx,
      Zero < Imag ]
    op _i : Rat -> Imag 
    op _i : NzRat -> NzImag 
    op -_ : Cpx -> Cpx 
    op -_ : NzCpx -> NzCpx 
    op _+_ : Cpx Cpx -> Cpx {assoc comm}
    op _+_ : NzRat NzImag -> NzCpx -- {assoc comm} CafeOBJ does not allow.
    op _*_ : Cpx Cpx -> Cpx 
    op _*_ : NzCpx NzCpx -> NzCpx 
    op _/_ : Cpx NzCpx -> Cpx 
    op _# : Cpx -> Cpx 
    op |_|^2 : Cpx -> Rat 
    op |_|^2 : NzCpx -> NzRat 
  }
  axioms {
    vars R S : Rat    vars R' R'' S' S'' : NzRat 
    vars A B C : Cpx 
    eq 0 i = 0 .
    eq C + 0 = C .
    eq (R i) + (S i) = (R + S) i .
    eq -(R' + (S' i)) = (- R') + ((- S') i ) .
    eq -(S' i) = (- S') i .
    eq R * (S i) = (R * S) i .
    eq (S i) * R = (R * S) i .
    eq (R i) * (S i) = - (R * S) .
    eq C * (A + B) = (C * A) + (C * B) .
    eq (A + B) * C = (C * A) + (C * B) .
    eq R # = R .
    eq (R' + (S' i))# = R' + ((- S') i) .
    eq (S' i) # = ((- S') i) .
    eq | C |^2 = C * (C #) .
    eq (S' i) / R'' = (S' / R'') i .
    eq (R' + (S' i)) / R'' = (R' / R'') + ((S' / R'') i) .
    eq A / (R' i) = A * (((- s 0) /  R') i) .
    eq A / (R'' + (R' i)) =
       A *((R'' / |(R'' + (R' i))|^2) + (((- R') / |(R'' + (R' i))|^2) i)).
  }
}


module! QUAT-RAT {
  protecting (CPX-RAT)
  signature {
    [ NzJ Zero < J < Quat,
      NzCpx < NzQuat Cpx < Quat,
      NzJ < NzQuat ]
    op _j : Cpx -> J 
    op _j : NzCpx -> NzJ 
    op -_ : Quat -> Quat 
    op _+_ : Quat Quat -> Quat {assoc comm}
    op _+_ : Cpx NzJ -> NzQuat -- {assoc comm} CafeOBJ does not allow
    op _*_ : Quat Quat -> Quat 
    op _*_ : NzQuat NzQuat -> NzQuat 
    op _/_ : Quat NzQuat -> Quat 
    op _# : Quat -> Quat 
    op |_|^2 : Quat -> Rat 
    op |_|^2 : NzQuat -> NzRat 
  }
  axioms {
    vars O P Q : Quat   vars B C : Cpx 
    vars C' : NzCpx
    eq 0 j = 0 .
    eq Q + 0 = Q .
    eq -(C + (B j)) = (- C) + ((- B) j ) .
    eq (C j) + (B j) = (C + B) j .
    eq C * (B j) = (C * B) j .
    eq (B j) * C = (B * (C #)) j .
    eq (C j) * (B j) = - (C * (B #)) .
    eq Q * (O + P) = (Q * O) + (Q * P) .
    eq (O + P) * Q = (O * Q) + (P * Q) .
    eq (P + Q) # = (P #) + (Q #) .
    eq (C j) # = (- C) j .
    eq | Q |^2 = Q * (Q #) .
    eq Q / (C' j) = Q * ((s 0 / (- C')) j) .
    eq Q / (C + (C' j)) = Q * (((C #) / |(C + (C' j))|^2) + 
       (((- C') / |(C + (C' j))|^2) j)) .
  }
}

module! TST {
  protecting (QUAT-RAT)
  ops 1 2 3 4 5 6 7 8 9 : -> NzNat
  eq 1 = s 0 .  eq 2 = s 1 .  eq 3 = s 2 .
  eq 4 = s 3 .  eq 5 = s 4 .  eq 6 = s 5 .
  eq 7 = s 6 .  eq 8 = s 7 .  eq 9 = s 8 .
}

select TST

reduce 3 + 2 .
reduce 3 * 2 .
reduce p p 3 .
reduce 4 > 8 .
reduce d(2,8) .
reduce quot(7,2) .
reduce gcd(9,6) .
reduce (- 4) + 8 .
reduce (- 4) * 2 .
reduce 8 / (- 2) .
reduce (1 / 3) + (4 / 6) . --> fail
reduce | 1 + (2 i) |^2 . --> fail
reduce | (1 + (3 i)) + (1 + ((- 2) i)) |^2 .
reduce (3 + ((3 i) + ((- 2) i))) / ((2 i) + 2) .
reduce (2 + ((3 i) j)) * ((5 i) + (7 j)) .
reduce (1 + ((1 i) j)) / (2 j) .  --> fail
--
eof
--
$Id: quat.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
