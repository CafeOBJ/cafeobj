require Msimple-nat

module! CHOICE-NAT {
  extending (SIMPLE-NAT)
  op _|_ : Nat Nat -> Nat
  vars N N' : Nat
  trans N | N' => N .
  trans N | N' => N' .
}

provide Mchoice-nat

eof
-- the followings are example of reduce/execute in manual
reduce s(0) | (s(s(0)) + s(s(s(0)))) .
execute s(0) | (s(s(0)) + s(s(s(0)))) .

** $Id: Mchoice-nat.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
