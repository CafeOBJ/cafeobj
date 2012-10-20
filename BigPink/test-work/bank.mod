** ----------------------------------------------------------------------
** bank.mod
** ----------------------------------------------------------------------
unprotect INT .
set include FOPL-CLAUSE on

mod! INT 
{
  signature {
    [ Int ]
    op 0 : -> Int
    op _+_ : Int Int -> Int
    op _-_ : Int Int -> Int
    pred _<=_ : Int Int
  }
  axioms {
    vars M N : Int
    ax M <= M .
    ax 0 <= M & 0 <= N -> 0 <= M + N .
    ax M <= N -> 0 <= N - M .
  }
}

mod* ACCOUNT {
  imports{
    protecting(INT)
  }
  signature{
    *[ Account ]*
    op new-account : -> Account
    bop balance : Account -> Int
    bop deposit : Int Account -> Account
    bop withdraw : Int Account -> Account
  }
  axioms{
    var A : Account    vars M N : Int

    eq balance(new-account) = 0 .
    ax 0 <= N -> balance(deposit(N,A)) = balance(A) + N .
    ax ~(0 <= N) -> balance(deposit(N,A)) = balance(A) .
    ax N <= balance(A) -> balance(withdraw(N,A)) = balance(A) - N .
    ax ~(N <= balance(A)) -> balance(withdraw(N,A)) = balance(A) .
  }
}

mod* PROOF {
  protecting(ACCOUNT)

  pred P : Account .
  #define P(A:Account) ::= 0 <= balance(A) .

-- goal [GOAL]: P(new-account) .
-- goal [GOAL]: \A[N:Int]\A[A:Account] P(A) -> P(deposit(N,A)) .  -- ok
-- goal [GOAL]: \A[N:Int]\A[A:Account] P(A) -> P(withdraw(N,A)) .  -- ok
}

option reset

flag(auto3,on)
flag(quiet,off)
flag(print-stats,on)
flag(universal-symmetry,on)
param(max-proofs,1)
param(stats-level,4)
open PROOF .
db reset

-- sos = { GOAL }

-- resolve .

check safety P from new-account 

close
**
eof
--
$Id:
