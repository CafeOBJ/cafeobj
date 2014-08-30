-- FILE: /home/diacon/LANG/Cafe/prog/counter.mod
-- CONTENTS: behavioural specification of a counter object featuring
--           a comparison between coinduction and context induction proofs,
--           behavioural rewriting specification, and
--           proof of a behavioural transition property
-- AUTHOR: Razvan Diaconescu
-- corrected by sawada@sra.co.jp
-- DIFFICULTY: ***

-- non-deterministic naturals in RWL
mod! NNAT {
  extending(NAT)
  op _|_ : Nat Nat -> Nat

  vars M N : Nat

  trans M | N => M .
  trans M | N => N .
}

-- generic data
mod* DATA {
  [ Data ]
  op _+_ : Data Data -> Data 
}  

-- generic counter object
mod* COUNTER(X :: DATA) {
  *[ Counter ]*    

  bop add : Data Counter -> Counter    -- method
  bop read_ : Counter -> Data          -- attribute

  eq read add(N:Data, C:Counter) = read(C) + N .  
}

-- proof of add(m,(add(n,counter))) =b= add(n,(add(m,counter))) .
open COUNTER(NAT) .
  ops m n : -> Nat .
  op counter : -> Counter .
--> PROOF BY CONTEXT INDUCTION
--> Base case: length of context is 1
red read add(m,(add(n,counter))) == read add(n,(add(m,counter))) .
--> Induction hypothesis: length of context read(c(z)) is n
  op c : Counter -> Counter .  
  eq read c(add(m,(add(n,counter)))) = read c(add(n,(add(m,counter)))) .
--> Induction step:
  op q : -> Nat .
red read add(q,c(add(m,(add(n,counter))))) ==
    read add(q,c(add(n,(add(m,counter))))) .
--> PROOF BY COINDUCTION
red add(m,add(n,counter)) =*= add(n,add(m,counter)) .
close

-- proof of beh transition add(m | n,counter) => add(m,counter)
-- for a non-deterministic counter (in a HOSRWL specification)
open COUNTER(NNAT{sort Data -> Nat}) .
  ops m n : -> Nat .
  op counter : -> Counter .
--> PROOF BY CONTEXT INDUCTION
--> Base case: length of context is 1
**> want to perform only transitions:
** set exec normalize off <- now this is obsolete switch.
** but this example rely on this setting.
evq (setq *cexec-normalize* nil)

red read add(m | n,counter) ==> read add(m,counter) .
--> Induction hypothesis: length of context read(c(z)) is n
  op c : Counter -> Counter .  
  eq read c(add(m | n,counter)) ==> read c(add(m,counter)) = true .
--> Induction step:
  op q : -> Nat .
red read add(q,c(add(m | n,counter))) ==> read add(q,c(add(m,counter))) .
--> PROOF BY CO-INDUCTION
red read add(m | n,counter) ==> read add(m,counter) .
close
** recover internal switch
evq (setq *cexec-normalize* t)
--
eof
--
$Id: counter.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
