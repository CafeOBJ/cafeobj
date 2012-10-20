** -*- Mode:CafeOBJ -*-
**> an exmaple induction in CafeOBJ
**> associativity of natural addition

module! NATERM {
  signature {
    [ Nat ]
    op 0 : -> Nat
    op s_ : Nat -> Nat
    op _+_ : Nat Nat -> Nat
  }
  axioms {
    vars M N : Nat 
    eq 0 + N = N .
    eq s M + N = s(M + N) .
  }
  -- psude variables.
  ops x y z : -> Nat 
}

module* NATF0 {
  pr (NATERM)
  op a : -> Nat 
}

module! GOAL(A :: NATF0) {
  pr (NATERM)
  op goal : -> Bool
  eq goal = ((a +(y + z)) == ((a + y)+ z)) .
}

module! HYP(A :: NATF0) {
  pr (NATERM)
  eq a +(y + z) = (a + y)+ z .
}

make IND (
(GOAL *{op goal -> base})[NATERM{op a -> 0}]
 + HYP[NATERM{op a -> x}] 
 + (GOAL *{op goal -> step})[NATERM{op a -> s x}]
)

red in IND : base and step .
--
eof
**
$Id: induction1.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
