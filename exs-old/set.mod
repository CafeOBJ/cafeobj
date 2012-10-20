** -*- Mode:CafeOBJ -*-
-- ===================================================================
-- SET
-- ===================================================================
module! BSET ( X :: TRIV ) {
  [ Set ]
  protecting (IDENTICAL)
  ops ({}) omega : -> Set
  op {_} : Elt -> Set
  op _+_ : Set Set -> Set { assoc comm id: ({}) }
  op _&_ : Set Set -> Set { assoc comm idem id: omega }
  vars S S' S'' : Set
  vars E E' : Elt
  eq S + S = {} .
  cq { E } & { E' } = {} if E =/= E' .
  eq S & {} = {} .
  cq S & (S' + S'') = (S  & S') + (S & S'') 
     if (S' =/== {}) and (S'' =/== {}) .
}

-- the new syntax of parameter uses "(", ")"
-- also, the instantiation uses "(", ")"
-- NOTE: current implementation supports old syntax.
--
module! SET ( X :: TRIV ) {
  protecting (BSET(X))
  protecting (INT)
  op _U_ : Set Set -> Set { assoc comm id: ({}) }
  op _-_ : Set Set -> Set
  op #_ : Set -> Int { prec: 0 }
  op _in_ : Elt Set -> Bool 
  op _in_ : Set Set -> Bool
  op empty?_ : Set -> Bool 
  var X : Elt
  vars S S' S'' : Set
  eq S U S' = (S & S') + S + S' .
  eq S - S' = S + (S & S') .
  eq empty? S = S == {} .
  eq X in S = { X } & S =/= {} .
  eq S in S' = S U S' == S' .
  eq # {} = 0 .
  cq #({ X } + S) = # S if X in S .
  cq #({ X } + S) = 1 + # S if not X in S .
}

provide set
-- EOF
eof
--
$Id: set.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
--
