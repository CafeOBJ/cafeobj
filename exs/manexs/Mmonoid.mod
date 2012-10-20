module* MONOID {
  [ M ]
  op e : -> M
  op _*_ : M M -> M
  vars X Y Z : M
  eq (X * Y) * Z = X * (Y * Z) .
  eq e * X = X .
  eq X * e = X .
}
provide Mmonoid

eof

** $Id: Mmonoid.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
