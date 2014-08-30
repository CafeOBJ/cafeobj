-- FILE: /home/diacon/LANG/Cafe/prog/bank-account.mod
-- CONTENTS: a bank account system specification featuring
--           concurrent object composition,
--           behavioural verification
--           automatic generation of case analysis by meta-level encoding
-- AUTHORS: Shuusaku Iida & Razvan Diaconescu
-- DIFFICULTY: ****

-- counter object
mod* COUNTER(X :: TRIV) {
  protecting(INT)

  *[ Counter ]*

  op init-counter : Elt -> Counter  -- initial state
  op no-counter : -> Counter        -- error
  bop add : Int Counter -> Counter  -- method
  bop amount_ : Counter -> Nat      -- attribute

  var ID : Elt
  var I : Int
  var C : Counter

  beq add(I, no-counter) = no-counter .
  eq amount init-counter(ID) = 0 .
  ceq amount add(I, C) = I + amount(C) if I + amount(C) >= 0 .
  ceq amount add(I, C) = amount(C) if I + amount(C) < 0 .
}

-- user identifiers
mod* USER-ID {
  [ UId ]
}

-- account object
mod* ACCOUNT {
  protecting(COUNTER(X <= view to USER-ID { sort Elt -> UId })
                     *{ hsort Counter -> Account,
                        op init-counter -> init-account,
                        op no-counter -> no-account })
}

-- system of accounts as a dynamic object
mod* ACCOUNT-SYS {
  protecting(ACCOUNT)

  *[ AccountSys ]*

  op init-account-sys : -> AccountSys
  bop add-account : UId Nat AccountSys -> AccountSys
  bop del-account : UId AccountSys -> AccountSys
  bop deposit : UId Nat AccountSys -> AccountSys
  bop withdraw : UId Nat AccountSys -> AccountSys
  bop balance : UId AccountSys -> Nat
  bop account : UId AccountSys -> Account {memo}

  vars U U' : UId
  var A : AccountSys
  var N : Nat

  eq account(U, init-account-sys) = no-account .
  ceq account(U, add-account(U', N, A)) = add(N, init-account(U))
       if U == U' .
  ceq account(U, add-account(U', N, A)) = account(U, A)
       if U =/= U' .
  ceq account(U, del-account(U', A)) = no-account
       if U == U' .
  ceq account(U, del-account(U', A)) = account(U, A)
       if U =/= U' .
  ceq account(U, deposit(U', N, A)) = add(N, account(U, A))
       if U == U' .
  ceq account(U, deposit(U', N, A)) = account(U, A)
       if U =/= U' .
  ceq account(U, withdraw(U', N, A)) = add(-(N), account(U, A))
       if U == U' .
  ceq account(U, withdraw(U', N, A)) = account(U, A)
       if U =/= U' .

  eq balance(U, A) = amount account(U, A) .
}

-- behavioural equivalence for the account object
mod BEQ-ACCOUNT {
  protecting(ACCOUNT)

  -- op _=*=_ : Account Account -> Bool { coherent }

  vars A1 A2 : Account

  eq A1 =*= A2 = amount(A1) == amount(A2) .
}

-- -------------------------------------------------------------
-- proof that =*= is hidden congruence
-- -------------------------------------------------------------
-- case 1: i + amount(a1) >= 0
open BEQ-ACCOUNT .
-- hypothesis
ops a1 a2 : -> Account .
op i : -> Int .
eq i + amount(a2) >= 0 = true .
-- eq a1 =*= a2 = true .
eq amount(a1) = amount(a2) .
red add(i, a1) =*= add(i, a2) .
close

-- case 2: i + amount(a1) < 0
open BEQ-ACCOUNT .
-- hypothesis
ops a1 a2 : -> Account .
op i : -> Int .
eq i + amount(a2) < 0 = true .
-- eq a1 =*= a2 = true .
eq amount(a1) = amount(a2) .
red add(i, a1) =*= add(i, a2) .
close

-- behavioural equivalence for the system of accounts
mod BEQ-ACCOUNT-SYS {
  protecting(BEQ-ACCOUNT)
  protecting(ACCOUNT-SYS)

  op _R[_]_ : AccountSys UId AccountSys -> Bool { coherent }

  vars BA1 BA2 : AccountSys
  var U : UId

  eq BA1 R[ U ] BA2 = account(U, BA1) =*= account(U, BA2) .
}

-- proof that withdraw(u, n, ba) =b= ba if the user u does not have any account
open BEQ-ACCOUNT-SYS .
  op ba : -> AccountSys .
  ops u u' : -> UId .
  op n : -> Nat .
-- assumption
  eq account(u, ba) = no-account .
red withdraw(u, n, ba) R[ u ] ba .
red withdraw(u, n, ba) R[ u' ] ba .
close


mod PROOF {
-- organize the proof of the behavioural property
  protecting(BEQ-ACCOUNT-SYS)

  op ba : -> AccountSys
  ops u u1 u2 : -> UId
  ops n1 n2 n01 n02 m1 m1' m2 m2' : -> Nat

-- atomic cases    
  eq n1 =/= 0 = true .
  eq n2 =/= 0 = true .
  eq n01 == 0 = true .
  eq n02 == 0 = true .
  eq n1 <= m1 = true .
  eq n01 <= m1 = true .
  eq n1 > m1' = true .
  eq n2 <= m2 = true .
  eq n02 <= m2 = true .
  eq n2 > m2' = true .

  op state-of-system : Nat Nat -> AccountSys
  ops W1W2 W2W1 : Nat Nat Nat Nat -> AccountSys
-- the meta-level encoding generating the proof term containing all cases
  op TERM : UId Nat Nat Nat Nat -> Bool
  op TERM1 : UId Nat Nat -> Bool 
  op TERM2 : UId -> Bool 
  op RESULT :  -> Bool 

  var U : UId 
  vars N1 N2 M1 M2 : Nat 

-- basic assumptions    
  eq state-of-system(M1, M2) = add-account(u1, M1,
	                       add-account(u2, M2, ba)) .

  eq W1W2(N1, N2, M1, M2) =
     withdraw(u1, N1, withdraw(u2, N2, state-of-system(M1, M2))) .

  eq W2W1(N1, N2, M1, M2) =
     withdraw(u2, N2, withdraw(u1, N1, state-of-system(M1, M2))) .

-- the parameterized proof term  
  eq TERM(U, N1, N2, M1, M2) = W1W2(N1, N2, M1, M2) R[U] W2W1(N1, N2, M1, M2) .

  eq TERM1(U, N2, M2) = TERM(U, n1, N2, m1, M2) and
                     TERM(U, n1, N2, m1', M2) and
		     TERM(U, n01, N2, m1, M2) .

  eq TERM2(U) = TERM1(U, n2, m2) and
                TERM1(U, n2, m2') and
		TERM1(U, n02, m2) .

  eq RESULT = TERM2(u) and TERM2(u1) and TERM2(u2) .
}

-- set tram path brute .
-- tram red RESULT .
-- tram reduce in PROOF : RESULT .
reduce in PROOF : RESULT .
eof
--
$Id: bank-account.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
