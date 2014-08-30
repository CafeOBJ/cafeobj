require Mmonoid
require Msimple-nat
require Mmult

view NAT-AS-MONOID from MONOID to SIMPLE-NAT {
  sort M -> Nat,
  op e -> 0,
  op _*_ -> _+_
}

view NAT-AS-MONOID' from MONOID to MULT {
  sort M -> Nat,
  op e -> s(0),
  op _*_ -> _*_
}

provide Mviews1
eof

** $Id: Mviews1.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
