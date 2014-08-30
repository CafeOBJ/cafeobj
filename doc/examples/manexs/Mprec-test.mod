module PREC-TEST {
  [ S ]
  op _+_ : S S -> S { prec: 33 }
  op _*_ : S S -> S { prec: 31 }
  op -_ : S -> S
} 

provide Mprec-test
--
eof
--
select PREC-TEST
parse X:S + Y:S * Z:S .
parse - X:S + Y:S .

** $Id: Mprec-test.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
