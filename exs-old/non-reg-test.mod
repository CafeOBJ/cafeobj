** -*- Mode:CafeOBJ -*-
--

**> setting varbose on
**> this will cause regularzing proc produce reports.
set verbose on
set regularize signature on

module  NON-REG1{
  [ S0 S1 S2, S0 < S1 S2 ]
  op _+_ : S1 S1 -> S1
  op _+_ : S2 S2 -> S2 
  attr _+_ { assoc prec: 15 }
  op _*_ : S2 S2 -> S2
  op _*_ : S1 S1 -> S1
  attr _*_ { assoc prec: 14 }
  op f : S1 S1 -> S1 
  op f : S2 S2 -> S2 
  op s0 : -> S0 
  op s1 : -> S1 
  op s2 : -> S2
}

module  NON-REG2 {
  [ S T U, T < U ]
  op c : -> S
  op c : -> U
  op f : T -> T
  op f : S -> S
  op g : U -> U
}

    
module  NON-REG3 {
  [ C < A B ]
  op c : -> A
  op c : -> B
  op _+_ : A A -> A
  op _+_ : B B -> B
}

**> setting verbose off
set regularize signature off
set verbose off
eof

-- $Id: non-reg-test.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
