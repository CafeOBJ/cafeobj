-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Mon, 25 May 98 13:06:17 JST
-- Message-Id: <9805250406.AA02837@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  the other cafeobj files for the jewels 
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 11472

-- Dear Toshimi,

-- These are the other running CafeOBJ files underlying the CafeOBJ
-- jewels.

-- Enjoy them!
-- Razvan

-- PS. For the bank account example I just noticed yesterday that it is
-- not running well anymore, maybe there is some problem newly introduced
-- by p7, but I am not yet sure about this. I asked Iida-san to
-- investigate about this.
-- --------------------------------------------------------
-- example of RWL specification handling non-determinism

mod! NNAT {
  extending(NAT)

  op _|_ : Nat Nat -> Nat { r-assoc }
  
  vars M N : Nat

  trans N | M => N .
  trans N | M => M .
}


--> proof of 3 <= ( 4 | 4 | 5 )
red ((3 <= ( 4 | 4 | 5 ))  ==> false) == true .
-- ----------------------------------------------------------
mod* NNAT-HSA {
  protecting(NAT)

  *[ NNat ]*

  op [_] : Nat -> NNat
  op _|_ : NNat NNat -> NNat { r-assoc coherent }
  bop _->_ : NNat Nat -> Bool

  vars S1 S2 : NNat
  vars M N : Nat

  eq [M] -> N = M == N .
  eq S1 | S2 -> N = S1 -> N or S2 -> N .
}

--> some tests
red ( [1] | [2] | [3] ) -> 2 .
red ( [1] | [2] | [3] ) -> 4 .

--> the behavioural equivalence is =*=
--  (already automatically proved by the system)  
--> s =*= s' == (forall n:Nat) s -> n iff s' -> n
--> but we can prove that =*= is a hidden congruence wrt _|_ too:
open NNAT-HSA .
  ops s1 s1' s2 s2' :  -> NNat .
  op n :  -> Nat .
--> s1 =*= s1' and s2 =*= s2'
-- normally the proof score should have been 
--   eq s1 =*= s1' = true .
--   eq s2 =*= s2' = true .
-- but there is a bug in CafeOBJ; hopefully this bug will be corrected
  var N : Nat
  eq s1 -> N = s1' -> N .
  eq s2 -> N = s2' -> N .

red (s1 | s2) -> n == (s1' | s2') -> n . 
close

open NNAT-HSA .
  ops s1 s2 s3 :  -> NNat .
  op n :  -> Nat . 
--> proof of commutativity
red (s1 | s2) -> n == (s2 | s1) -> n .
--> proof of associativity
red ((s1 | s2) | s3) -> n == (s1 | (s2 | s3)) -> n .
--> proof of idempotence
--> by lemma on idempotence on or
  eq B:Bool or B = B .
red (s1 | s1) -> n == s1 -> n .
close

mod* NNAT-HSA<= {
  protecting(NNAT-HSA)

  bop _<=_ : NNat Nat -> Bool

  vars M N : Nat 
  vars S1 S2 : NNat 
    
  eq [M] <= N = M <= N .
  eq S1 | S2 <= N = S1 <= N and S2 <= N .
}

red ([1] | [2] | [3]) <= 3 .
red ([1] | [2] | [3]) <= 1 .

mod* NNAT-HSA<=< {
  protecting(NNAT-HSA)

  op _<=_ : NNat NNat -> Bool
    
  vars M N : Nat 
  vars S1 S2 S : NNat 

  eq [M] <= [N] = M <= N .
  eq S1 | S2 <= S = (S1 <= S) and (S2 <= S) .
  eq S <= S1 | S2 = (S <= S1) and (S <= S2) .
}

open NNAT-HSA<=< .
red ([1] | [2] | [3]) <= ([4] | [4] | [5]) .
red ([1] | [2] | [3]) <= ([4] | [4] | [2]) .
close

mod* NNAT-HSA1 {
  protecting(NNAT-HSA)

  op _|_ : NNat Nat -> NNat { coherent } 

  beq S:NNat | N:Nat = S | [N] .
}
** ------------------------------------------------------------
mod* LIST (X :: TRIV) {

   [ Elt < Elt* ]

  op error : -> Elt*
    
  *[ List ]*

  op nil : -> List   
  op cons : Elt List -> List   {coherent}
  bop car : List -> Elt* 
  bop cdr : List -> List
  bop _in_ : Elt List -> Bool 
    
  vars E E' : Elt
  var L : List

  eq car(cons(E, L)) = E .
  eq car(nil) = error .
  beq cdr(cons(E, L)) = L .
  eq E in cons(E', L) = (E == E') or (E in L) .
  eq E in nil = false . 
}

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod* LIST* {
  protecting(LIST + BARE-NAT)

  bop cdr : Nat List -> List

  eq cdr(0, L:List) = L .
--  eq cdr(s(N:Nat), L:List) = cdr(cdr(N, L)) .
  eq cdr(s(N:Nat), L:List) = cdr(N, cdr(L)) .
}

mod* LIST-BEH-EQUIV {
  protecting(LIST*)

  op _R[_,_]_ : List Nat Elt List -> Bool {coherent}

  var N : Nat
  var E : Elt
  vars L L' : List 
    
  eq L R[N,E] L' = car(cdr(N, L)) == car(cdr(N, L')) and
                 (E in cdr(N, L)) == (E in cdr(N, L')) .
}

** proof score for behavioural coherence of cons(_)
** when you run it you should COMMENT OUT the coherence declaration of cons
open .
  op n :  -> Nat .
  ops l l' :  -> List .
  ops e e' :  -> Elt .
** hypothesis
  beq l = l' .
** behavioural coherence of cons(_) by case analysis 
red cons(e, l) R[0,e]   cons(e, l') .
red cons(e, l) R[(s n),e] cons(e, l') .
red cons(e, l) R[0,e']   cons(e, l') .
red cons(e, l) R[(s n),e'] cons(e, l') .
close

mod* BASICSETS (X :: TRIV) {
  protecting(PROPC)

  *[ Set ]*

  op empty : -> Set 
  op add   : Elt Set -> Set  {coherent}
  bop _in_  : Elt Set -> Bool  

  vars E E' : Elt
  var S : Set 

  eq E in add(E', S) = (E == E') or (E in S) .
  eq E in empty = false .
}

** proof score for  behavioural coherence of add(_)
** when you run this you should COMMENT OUT the coherence declaration of add(_)
open .
  ops e e' :  -> Elt .
  ops s s' :  -> Set .
** hypothesis
  beq s = s' .
** behavioural coherence of add(_) by case analysis
red e  in add(e, s)  == e  in add(e, s') .
red e' in add(e, s)  == e' in add(e, s') .
close

mod* SETS {
  protecting(BASICSETS)
  
  op _U_ : Set Set -> Set  {coherent}
  op _&_ : Set Set -> Set  {coherent}
  op not : Set -> Set      {coherent}

  var E : Elt
  vars S1 S2 : Set
    
  eq E in S1 U S2  = (E in S1)  or (E in S2) .
  eq E in S1 & S2  = (E in S1) and (E in S2) .
  eq E in not(S1)  = not (E in S1) .
}

** proof score for beh coherence of _U_, _&_, and not(_)
** when you run this you should COMMENT OUT the corresponding coherence
** declarations
open .
  ops s1 s2 s1' s2' : -> Set .
  op e : -> Elt .
** by theorem of constants
  ceq S1 =*= S2 = true if (e in S1) == (e in S2) .
** hypothesis
  beq s1 = s1' .
  beq s2 = s2' .
** beh coherence of _U_
red (s1 U s2) =*= (s1' U s2') .
** beh coherence of _&_
red (s1 & s2) =*= (s1' & s2') .
** beh coherence of not_
red (not(s1)) =*= (not(s1')) .
close

** *************************** ***
**> Some behavioral properties ***
** *************************** ***
open .
  op e : -> Elt .
  ops s1 s2 s3 : -> Set .
** by theorem of constants
  ceq S1 =*= S2 = true if (e in S1) == (e in S2) .
**> commutativity of _U_
red (s1 U s2) =*= (s2 U s1) .
**> associativity of _U_
red (s1 U (s2 U s3)) =*= ((s1 U s2) U s3) .
**> idempotency of _U_
red (s1 U s1) =*= s1 .
**> empty is the unity of _U_
red (empty U s1) =*= s1 .
**> commutativity of _&_
red (s1 & s2) =*= (s2 & s1) .
**> associativity of _&_
red (s1 & (s2 & s3)) =*= ((s1 & s2) & s3) .
**> idempotency of _&_
red (s1 & s1) =*= s1 .
**> empty & S is empty
red (empty & s1) =*= empty .
**> distributivity
red (s1 & (s2 U s3)) =*= ((s1 & s2) U (s1 & s3)) .
red (s1 U (s2 & s3)) =*= ((s1 U s2) & (s1 U s3)) .
**> de Morgan laws
red not(s1 U s2) =*= (not(s1) & not(s2)) . 
red not(s1 & s2) =*= (not(s1) U not(s2)) . 
**> double negation
red not(not(s1)) =*= s1 .
close
-- ---------------------------------------------------------------------
-- FILE: /home/diacon/LANG/Cafe/prog/bank-account.mod
-- CONTENTS: a bank account system specification featuring
--           concurrent object composition,
--           behavioural verification
--           automatic generation of case analysis by meta-level encoding
-- AUTHORS: Shuusaku Iida & Razvan Diaconescu
-- DIFFICULTY: ****

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

mod* USER-ID {
  [ UId ]
}

mod* ACCOUNT {
  protecting(COUNTER(X <= view to USER-ID { sort Elt -> UId })
                     *{ hsort Counter -> Account,
                        op init-counter -> init-account,
                        op no-counter -> no-account })
}

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

mod BEQ-ACCOUNT {
  protecting(ACCOUNT)

--  op _=*=_ : Account Account -> Bool { coherent }

  vars A1 A2 : Account

  eq A1 =*= A2 = amount(A1) == amount(A2) .
}

-- -------------------------------------------------------------
-- prove that the =*= is hidden congruence
-- -------------------------------------------------------------
-- case 1: i + amount(a1) >= 0
open BEQ-ACCOUNT
-- hypothesis
ops a1 a2 : -> Account .
op i : -> Int .
eq i + amount(a2) >= 0 = true .
-- eq a1 =*= a2 = true .
eq amount(a1) = amount(a2) .
red add(i, a1) =*= add(i, a2) .
close

-- case 2: i + amount(a1) < 0
open BEQ-ACCOUNT
-- hypothesis
ops a1 a2 : -> Account .
op i : -> Int .
eq i + amount(a2) < 0 = true .
-- eq a1 =*= a2 = true .
eq amount(a1) = amount(a2) .
red add(i, a1) =*= add(i, a2) .
close

mod BEQ-ACCOUNT-SYS {
  protecting(BEQ-ACCOUNT)
  protecting(ACCOUNT-SYS)

  op _R[_]_ : AccountSys UId AccountSys -> Bool { coherent }

  vars BA1 BA2 : AccountSys
  var U : UId

  eq BA1 R[ U ] BA2 = account(U, BA1) =*= account(U, BA2) .
}

open BEQ-ACCOUNT-SYS
op ba : -> AccountSys .
ops u u' : -> UId .
op n : -> Nat .

eq account(u, ba) = no-account .

red withdraw(u, n, ba) R[ u ] ba .
red withdraw(u, n, ba) R[ u' ] ba .
close

mod PROOF {
  protecting(BEQ-ACCOUNT-SYS)

  op ba : -> AccountSys
  ops u u1 u2 : -> UId
  ops n1 n2 n01 n02 m1 m1' m2 m2' : -> Nat

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
  op TERM : UId Nat Nat Nat Nat -> Bool
  op TERM1 : UId Nat Nat -> Bool 
  op TERM2 : UId -> Bool 
  op RESULT :  -> Bool 

  var U : UId 
  vars N1 N2 M1 M2 : Nat 

  eq state-of-system(M1, M2) = add-account(u1, M1,
	                       add-account(u2, M2, ba)) .

  eq W1W2(N1, N2, M1, M2) =
     withdraw(u1, N1, withdraw(u2, N2, state-of-system(M1, M2))) .

  eq W2W1(N1, N2, M1, M2) =
     withdraw(u2, N2, withdraw(u1, N1, state-of-system(M1, M2))) .

  eq TERM(U, N1, N2, M1, M2) = W1W2(N1, N2, M1, M2) R[U] W2W1(N1, N2, M1, M2) .

  eq TERM1(U, N2, M2) = TERM(U, n1, N2, m1, M2) and
                     TERM(U, n1, N2, m1', M2) and
		     TERM(U, n01, N2, m1, M2) .

  eq TERM2(U) = TERM1(U, n2, m2) and
                TERM1(U, n2, m2') and
		TERM1(U, n02, m2) .

  eq RESULT = TERM2(u) and TERM2(u1) and TERM2(u2) .
}

red RESULT .
