** -*- Mode:CafeOBJ -*-

module* FN {
  [ S ]  op f : S -> S 
}

module! 2(F :: FN) {
  op xx : S -> S 
  var X : S 
  eq xx(X) = f(f(X)) .
}

provide 2
eof
--
$Id: 2.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $ 
