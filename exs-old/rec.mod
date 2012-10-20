** -*- Mode:CafeOBJ -*-
-- recursion in CafeOBJ
--
**> this is file: exs/rec.mod translated from ~goguen/obj/exs/rec.obj

module! PEANO
     principal-sort Nat
{
  [ Nat ]
  op 0 : -> Nat 
  op s_ : Nat -> Nat 
}

module! PEANO1 
     principal-sort Nat
{
  extending (PEANO)
  ops id z : Nat -> Nat 
  op s1 : Nat Nat -> Nat
  vars N M : Nat 
  eq id(N) = N .
  eq z(N) = 0 .
  eq s1(N,M) = s(M) .
}

module* NATF0 
     principal-sort Nat
{
  extending (PEANO)
  op a : -> Nat 
}

module* NATF1 
     principal-sort Nat
{
  extending (PEANO)
  op b : Nat -> Nat
}

module* NATF2 
     principal-sort Nat
{
  extending (PEANO)
  op c : Nat Nat -> Nat
}

module! REC(X :: NATF1, Y :: NATF2)
{
  extending (PEANO)
  op f : Nat Nat -> Nat 
  vars N M : Nat 
  eq f(0,N) = b(N).
  eq f(s(N),M) = c(M,f(N,M)).
}

module! NAT1 {
  protecting (PEANO1)
  protecting ((REC * { op f -> add })(X <= PEANO1{op b -> id},
				      Y <= PEANO1{op c -> s1}))
}
 
module! NAT' {
  protecting (NAT1)
  protecting ((REC * { op f -> mult })(X <= PEANO1{op b -> z},
				       Y <= NAT1{op c -> add}))
}

select NAT'

red add(s s 0, s s 0).
red mult(s s 0, s s 0).
red add(s s s 0, s s 0).
red mult(s s s 0, s s 0).

--
eof
--
$Id: rec.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
