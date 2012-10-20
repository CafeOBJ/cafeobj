** -*- Mode:CafeOBJ -*-

module! NAT? {
  extending (NAT)
  op _?_ : Nat Nat -> Nat

  vars M N : Nat
  trans M ? N => M .
  trans M ? N => N .
}

module* DATA {
  [ Data ]
  op _+_ : Data Data -> Data { assoc comm }
}

module* GENERIC-COUNTER(X :: DATA){
  *[ Counter ]*
  bop add : Data Counter -> Counter
  bop read_ : Counter -> Data

  var N : Data
  var C : Counter

  eq read add(N,C) = N + read C .
}

module* COUNTER {
  protecting (GENERIC-COUNTER[NAT{sort Data -> Nat}])
}

module* NCOUNTER {
  protecting (GENERIC-COUNTER[NAT?{sort Data -> Nat}])
}

--
eof
--
$Id: rwl-ex1.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
