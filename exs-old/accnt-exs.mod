** -*- Mode:CafeOBJ -*-
--

** an example -------------------------------------------------------
-- red debit(Paul,50) < Paul : Accnt | (bal = 250) > credit(Paul,300)
--     < Peter : Accnt | bal = 300 > debit(Peter, 200)
--     credit(Paul, 300) < Mary : Accnt | bal = 12560 >
--     credit(Mary, 260) .
--  ------------------------------------------------------------------
-- red debit(Paul,50) < Paul : Accnt | (bal = 250) > credit(Paul,300)
--     < Peter : Accnt | bal = 300 > debit(Peter, 200)
--    credit(Paul, 300) < Mary : Accnt | bal = 12560 >
--    credit(Mary, 260) .

require account

select ACCOUNT
** similar to above, but objects are made persistent. 
exec delete < Paul : Accnt > .
exec delete < Peter : Accnt > .
exec delete < Mary : Accnt > .
--> red makeAccnt(Paul, (bal = 250)) .
exec makeAccnt(Paul, (bal = 250)) .
--> red makeAccnt(Peter, (bal = 300)) .
exec makeAccnt(Peter, (bal = 300)) .
--> red make-Accnt(Mary, (bal = 12560)) .
exec makeAccnt(Mary, (bal = 12560)) .

exec debit(Paul,50) (< Paul : Accnt >)
  credit(Paul, 300) (< Peter : Accnt >) debit(Peter, 200)
  credit(Paul, 300) (< Mary : Accnt >) credit(Mary, 260) .

--> see the current status 
red < Paul : Accnt > .
red < Peter : Accnt > .
red < Mary : Accnt > .
--
eof
--
$Id: accnt-exs.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
