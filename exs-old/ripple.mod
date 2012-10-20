** -*- Mode:CafeOBJ -*-

module! INT-EX {
  signature {
    [ Int Nat, Nat < Int ]
    ops 0 1 2 : -> Nat 
    op s_ : Nat -> Nat 
    attr s_ {prec 1}
    op s_ : Int -> Int 
    op p_ : Int -> Int 
    attr p_ {prec: 1}
    op _+_ : Nat Nat -> Nat
    attr _+_ {assoc comm prec: 3}
    op _+_ : Int Int -> Int
    op _*_ : Nat Nat -> Nat 
    attr _*_ {assoc comm prec: 2}
    op _*_ : Int Int -> Int
    op _-_ : Int Int -> Int
    attr _-_ {prec: 4}
    op -_ : Int -> Int
    attr -_ {prec: 1}
    op 2**_ : Nat -> Nat
    attr 2**_ {prec: 1}
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

module! BUS {
  [ Bus ]
  extending (PROPC)
  extending (INT-EX)
  [ Prop < Bus ]
  op __ : Prop Bus -> Bus 
  op |_| : Bus -> Nat.INT-EX
  var B : Prop 
  var W : Bus 
  eq | B | = 1 .
  eq | B W | = s | W | .
  op #_ : Bus -> Int ** is really -> Nat.INT-EX
  attr #_ { prec: 1 }
  eq # false = 0 .
  eq # true = 1 .
  eq #(B W) = 2** | W | * # B + # W .
}

**> full adder
module! FADD {
  extending (PROPC) 
  ops cout sout : Prop Prop Prop -> Prop 
  attr cout/3 { strat: (0 1 2 3) }
  attr sout/3 { strat: (0 1 2 3) }
  vars I1 I2 C : Prop 
  eq sout(I1,I2,C) =  I1 xor I2 xor C .
  eq cout(I1,I2,C) = I1 and I2 xor I1 and C xor I2 and C .
}

**> n-bit ripple carry adder
module! NADD {
  protecting (FADD)
  protecting (BUS)
  ops cout sout : Bus Bus -> Prop 
  op sout* : Bus Bus -> Bus 
  vars B1 B2 : Prop 
  vars W1 W2 : Bus 
  eq cout(B1,B2) = cout(B1,B2,false) .
  eq sout(B1,B2) = sout(B1,B2,false) .
  eq cout(B1 W1,B2 W2) = cout(B1,B2,cout(W1,W2)) .
  eq sout(B1 W1,B2 W2) = sout(B1,B2,cout(W1,W2)) .
  eq sout*(B1,B2) = sout(B1,B2) .
  eq sout*(B1 W1,B2 W2) = sout(B1 W1,B2 W2) sout*(W1,W2) .
}

module! LEMMAS {
  protecting (NADD) 
  vars B1 B2 : Prop 
  eq #(B1 and B2) = # B1 * # B2 .
  eq #(B1 xor B2) = # B1 + # B2 - #(B1 and B2)* 2 .
  ** would write up if # : Bus -> Nat .
  vars W1 W2 : Bus 
  ceq | sout*(W1,W2)| = | W1 | if | W1 | == | W2 | .
}

**> base case
module! VARS {
  extending (LEMMAS)
  ops b1 b2 : -> Prop 
}

reduce in VARS : # sout*(b1,b2) + # cout(b1,b2) * 2 == # b1 + # b2 .

**> induction step
module! INDHYP {
  ex (LEMMAS)
  ops b1 b2 : -> Prop 
  ops w1 w2 : -> Bus 
  op n : -> Nat.INT-EX
  eq | w1 | = n .
  eq | w2 | = n .
  eq # sout*(w1,w2) + 2** n * # cout(w1,w2) = # w1 + # w2 .
}


reduce in INDHYP : #(b1 w1)+ #(b2 w2) ==  # sout*(b1 w1,b2 w2) + 2** | b1 w1 | * # cout(b1 w1,b2 w2) .

--
eof
--
$Id: ripple.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
