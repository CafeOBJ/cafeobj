** -*- Mode:CafeOBJ -*-

module! NAT-REVERSE {
  [ NzNat < Nat < Tree ]
  op 0 : -> Nat
  op s_ : Nat -> NzNat
  op p_ : NzNat -> Nat
  op _+_ : Nat Nat -> Nat { comm }
  op _^_ : Tree Tree -> Tree
  op rev : Tree -> Tree

  eq p s N:Nat = N .
  eq N:Nat + 0 = N .
  eq (s N:Nat) + (s M:Nat) = s s (N + M) .
  eq rev(N:Nat) = N .
  eq rev(T:Tree ^ T':Tree) = rev(T') ^ rev(T) .
}

select NAT-REVERSE
--> an example
parse (s s 0 + s 0 ^ s 0)^(s s 0) .
--> show tree .
show tree .
red rev((s s 0 + s 0 ^ s 0)^(s s s 0)) .
--> show tree .
show tree .

--
eof
--
$Id: reverse.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
