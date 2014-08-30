require Msimple-nat

module STACK-OF-NAT {
  [ NeStack < Stack ]
  protecting (SIMPLE-NAT) 
  op empty : -> Stack
  op push : Nat Stack -> NeStack
  op top_ : NeStack -> Nat
  op pop_ : NeStack -> Stack
  eq top push(X:Nat, S:Stack) = X .
  eq pop push(X:Nat, S:Stack) = S .
}

--
eof
--
select STACK-OF-NAT
parse top push(s(s(0)), empty) .
let 2 = s(s(0)) .
reduce top push(2,empty) .
parse top pop push(s(0), push(s(s(0)), empty)) .
reduce top pop push(s(0), push(s(s(0)), empty)) .
parse top pop push(s(0), empty) .
reduce top pop push(s(0), empty) .

** $Id: Mstack-of-nat.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
