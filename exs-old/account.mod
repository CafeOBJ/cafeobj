** -*- Mode: CafeOBJ -*-

** you can use `blocked comments' as the following:

" ** =============================================================================
-- 
-- 	Chaos source file for the module ACCOUNT
-- 
** -----------------------------------------------------------------------------
"
  
set include RWL off

module ACCOUNT {
  imports {
    protecting (ACZ-CONFIGURATION)
    protecting (INT)
  }
				   
  signature {
  -- Class Accnt --------------------------------------
    class Accnt {
      bal : Int
    }

    op credit : ObjectId Int -> AccntMessage
    op debit : ObjectId Int -> AccntMessage
    op transfer_from_to_ : Int ObjectId ObjectId -> AccntMessage

    op credit2 : Accnt Int -> Accnt
    op debit2  : Accnt Int -> Accnt

    op credit3 : ObjectId Int -> Accnt
    op debit3  : ObjectId Int -> Accnt
  }

  axioms {				 -- Rewrite rules
    vars A B : ObjectId
    vars M N N' : Int 
  
    trans [credit]:
      credit(A,M) < A : Accnt | bal = N > => < A : Accnt | bal = (N + M) > .
    eq [credit2]:
      credit2(< A : Accnt | bal = N >, M) = < A : Accnt | bal = (N + M) > .
    eq [credit3]:
      credit3(A, M) = set-bal(< A : Accnt >, M + bal(< A : Accnt >)) .

    ctrans [debit]:
	debit(A,M) < A : Accnt | bal = N > 
	=> < A : Accnt | bal = (N - M) > if N >= M .
    ceq [debit2]:
        debit2(< A : Accnt | bal = N >, M)
	= < A : Accnt | bal = N - M > if N >= M .   
    -- [trans]
    ctrans (transfer M from A to B)
	  < A : Accnt | (bal = N) > < B : Accnt | (bal = N') >
	    => < A : Accnt | (bal = (N - M)) > < B : Accnt | (bal = (N' + M)) >
	     if N >= M .
    trans (transfer M from A to B) => debit(A, M) credit(B,M) .
    }
}

--
set include RWL on
provide account
--
eof
**
$Id: account.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
