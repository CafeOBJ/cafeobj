require Msubtract

module* ACCOUNT {
  protecting (SUBTRACT)
  *[ Account ]*
  bops deposit withdraw : Account Nat -> Account
  bops balance point : Account -> Nat
  var N : Nat
  var A : Account
  eq balance(deposit(A, N)) = balance(A) + N .
  eq balance(withdraw(A, N)) = balance(A) - N .
  eq point(deposit(A, N)) = point(A) + s(0) .
}

provide Maccount

eof
--
** $Id: Maccount.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
