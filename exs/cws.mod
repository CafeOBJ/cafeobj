-- FILE: /home/diacon/LANG/Cafe/prog/cws.mod
-- CONTENTS: behavioural specification of a counter with switch object
--           featuring concurrent object composition with synchronization
-- AUTHOR: Shuusaku Iida
-- DIFFICULTY: ***

-- -------------------------------------------------------------
-- ON-OFF
-- -------------------------------------------------------------
mod! ON-OFF {
  [ Value ]

  ops on off : -> Value
}

-- -------------------------------------------------------------
-- SWITCH
-- -------------------------------------------------------------
mod* SWITCH {
  protecting(ON-OFF)

  *[ Switch ]*

  op init : -> Switch
  bop on_ : Switch -> Switch     -- method
  bop off_ : Switch -> Switch    -- method
  bop state_ : Switch -> Value   -- attribute

  var S : Switch

  eq state init = off .
  eq state(on S) = on .
  eq state(off S) = off .
}

-- -------------------------------------------------------------
-- COUNTER
-- -------------------------------------------------------------
mod* COUNTER {
  protecting(INT)

  *[ Counter ]*

  op init : -> Counter
  bop add : Int Counter -> Counter    -- method
  bop read : Counter -> Int          -- attribute

  var I : Int
  var C : Counter

  eq read(init) = 0 .
  eq read(add(I, C)) = I + read(C) .
}

-- --------------------------------------------
-- concurrent connection of  SWITCH and COUNTER
-- --------------------------------------------
mod* COUNTER-WITH-SWITCH {
  protecting(SWITCH + COUNTER)

  *[ Cws ]*

  op init : -> Cws
  bop put : Int Cws -> Cws             -- method
  bop add_ : Cws -> Cws                -- method
  bop sub_ : Cws -> Cws                -- method
  bop read : Cws -> Int               -- attribute 
  bop counter_ : Cws -> Counter    -- projection function
  bop switch_ : Cws -> Switch      -- projection function

  var N : Int
  var C : Cws

  eq read(C) = read(counter C) .  -- abbreviation equation for "read"

-- -------------------------------------
-- equations for switch
-- -------------------------------------
  eq switch(init) = init .
  eq switch put(N, C) = switch C .
  eq switch add(C) = on(switch C) .
  eq switch sub(C) = off(switch C) .

-- -------------------------------------
-- equations for counter
-- -------------------------------------
  eq counter(init) = init .
  ceq counter(put(N, C)) = add(N, counter(C))
       if state(switch(C)) == on .
  ceq counter(put(N, C)) = add(-(N), counter(C))
       if state(switch(C)) == off .
  eq counter add(C) = counter C .
  eq counter sub(C) = counter C .
}

-- -----------------------------------------------------------------
-- proof module (adding hidden equivalence relation to
-- COUNTER-WITH-SWITCH)
-- -----------------------------------------------------------------
module CWS-PROOF {
  protecting (COUNTER-WITH-SWITCH)
  bop addc : Int Cws -> Cws           -- a derived method

-- -------------------------------------
-- eqns for the derived method addc
-- -------------------------------------
  var C : Cws
  var N : Int

  ceq addc(N, C) = put(N, C) if state(switch C) == on .
  ceq addc(N, C) = put(-(N), C) if state(switch C) == off .

-- the behavioural equivalence
  op _R_ : Cws Cws -> Bool   { coherent }
  vars C1 C2 : Cws

  eq C1 R C2 =  switch(C1) =*= switch(C2) and
               counter(C1) =*= counter(C2) .

-- a lemma
  eq -(- N) = N .
}

--> ---------------------------------------------------------------
--> sub put(m, add put(n, sub init)) R  put(n, sub put(m, add init))
--> ---------------------------------------------------------------
open CWS-PROOF .
ops m n : -> Nat .
--> should be true
red sub(put(m, add(put(n, sub(init))))) R put(n, sub(put(m, add(init)))) .
--> should be true
red read(put(m, add(put(n, sub(init))))) ==
    read(put(n, sub(put(m, add(init))))) .
close

-- ------------------------------------------------------
-- Theorem: COUNTER-WITH-SWITCH is a (correct) concurrent 
--          conection of SWITCH and COUNTER
-- ------------------------------------------------------
-- the synchronization part consists only of a hidden sort
-- the synchronization morphisms are obvious
-- the morphism \psi_1 : SWITCH -> COUNTER-WITH-SWITCH is:
-- --  init  -> init
-- --  on    -> add
-- --  off   -> sub
-- --  state -> state switch
-- the morphism \psi_2 : COUNTER -> COUNTER-WITH-SWITCH is:
-- --  init -> init
-- --  add  -> addc  ** defined in CWS-PROOF
-- --  read -> read

--> prove that COUNTER-WITH-SWITCH refines COUNTER via \psi_2

open CWS-PROOF .
op c : -> Cws .
op n : -> Int .
--> case 1: state(switch c) = on .
eq state(switch c) = on .

red read(addc(n, c)) == n + read(c) .
close

open CWS-PROOF .
op c : -> Cws .
op n : -> Int .
--> case 2: state(switch c) = off .
eq state(switch c) = off .

red read(addc(n, c)) == n + read(c) .
close

--> prove that COUNTER-WITH-SWITCH refines SWITCH via \psi_1

open CWS-PROOF .
op c : -> Cws .
op n : -> Int .

red state switch add(c) == on .
red state switch sub(c) == off .
close

--> prove the commutativity eqns corresponding to the methods
open CWS-PROOF .
op c : -> Cws .
op n : -> Int .
--> case 1: 
eq state(switch c) = on .
red add(addc(n, c)) R addc(n, add(c)) .
red sub(addc(n, c)) R addc(n, sub(c)) .
close

open CWS-PROOF .
op c : -> Cws .
op n : -> Int .
--> case 2: state(switch c) = off .
eq state(switch c) = off .
red add(addc(n, c)) R addc(n, add(c)) .
red sub(addc(n, c)) R addc(n, sub(c)) . 
close

--> prove the commutativity eqns corresponding to the attributes
open CWS-PROOF .
op c : -> Cws .
op n : -> Int .
red state(switch put(n, c)) == state(switch c) .
red read(counter add(c)) == read(counter c) .
red read(counter sub(c)) == read(counter c) .
close
--
eof
--
$Id: cws.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
