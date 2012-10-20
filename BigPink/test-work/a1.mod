** simple a1
module N
{ [Nat]
  op 0 : -> Nat { constr }
  op s : Nat -> Nat { constr }
  op _+_ : Nat Nat -> Nat
  vars x y : Nat
  eq x + 0 = x .
  eq x + s(y) = s(x + y).
}

** $Id:
