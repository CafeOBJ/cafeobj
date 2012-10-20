-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Tue, 28 Oct 97 17:21:01 JST
-- Message-Id: <9710280821.AA02498@is27e0s07.jaist.ac.jp>
-- To: dlucanu@infoiasi.ro
-- Subject:  Re: methoology for concurrent object composition
-- Cc: ishisone@sra.co.jp, kokichi@jaist.ac.jp, nakagawa@sra.co.jp,
--         ogata@jaist.ac.jp, s_iida@jaist.ac.jp, sawada@sra.co.jp,
--         vec@funinf.math.unibuc.ro
-- Content-Type: text
-- Content-Length: 7153

-- : > BTW, just running it under v 1.4 gave lots of *false*, but this is due
-- : > to some bugs introduced by the reformed implementation of
-- : > rewriting. Hopefully these will be corrected soon. 
-- :
-- : I tried to use the beh equiv R for proving beh eqns but running it under
-- : v 1.3 I got some unexpected *false*'s. It will be interesting to do that
-- : under v 1.4 to see if it is OK.

-- Now with 1.4b3 it seems OK. I think there was a problem with some Nat
-- instead of Int for "put". I made everything Int instead of Nat and
-- there is no problem anymore.

-- This is the latest version.

-- Best regards,
-- Razvan
-- ------------------------------------------------
-- example of concurrent object composition in behavioural specification

set auto context on .

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
  bop read_ : Counter -> Int          -- attribute

  var I : Int
  var C : Counter

  eq read init = 0 .
  eq read add(I, C) = I + read C .
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
  bop read_ : Cws -> Int               -- attribute 
  bop counter_ : Cws -> Counter    -- projection function
  bop switch_ : Cws -> Switch      -- projection function

  var N : Int
  var C : Cws

  eq read C = read(counter C) .  -- abbreviation equation for "read"

-- -------------------------------------
-- behavioural equations for switch
-- -------------------------------------
  beq switch(init) = init .
  beq switch put(N, C) = switch C .
  beq switch add(C) = on(switch C) .
  beq switch sub(C) = off(switch C) .

-- -------------------------------------
-- behavioural equations for counter
-- -------------------------------------
  beq counter(init) = init .
  bceq counter(put(N, C)) = add(N, counter(C))
       if state(switch(C)) == on .
  bceq counter(put(N, C)) = add(-(N), counter(C))
       if state(switch(C)) == off .
  beq counter add(C) = counter C .
  beq counter sub(C) = counter C .
}

-- -----------------------------------------------------------------
-- proof module (adding hidden equivalence relation to
-- COUNTER-WITH-SWITCH)
-- -----------------------------------------------------------------
module CWS-PROOF {
  protecting(COUNTER-WITH-SWITCH)
  bop addc : Int Cws -> Cws           -- a derived method

-- -------------------------------------
-- beh eqns for the derived method addc
-- -------------------------------------
  var C : Cws
  var N : Int

  bceq addc(N, C) = put(N, C) if state(switch C) == on .
  bceq addc(N, C) = put(-(N), C) if state(switch C) == off .

-- R is a hidden equivalence relation
  op _R_ : Cws Cws -> Bool
  vars C1 C2 : Cws

  eq C1 R C2 =  switch(C1) =*= switch(C2) and
               counter(C1) =*= counter(C2) .

-- a lemma
  eq -(- N) = N .
}

--> -----------------------------------------------------------------
--> prove R is a congruence
--> -----------------------------------------------------------------
open CWS-PROOF

ops c c1 c2 : -> Cws .
op n : -> Nat .
op i : -> Int .

--> "a" can take any value of {on, off}, and the spec is symmetrical wrt
--> on and off, so we can uncomment the 1st and comment the 2nd
let a = on .
-- let a = off .

--> eq s1 R s2 = true .
-- eq switch(c1) =*= switch(c2) = true .
eq state(switch(c1)) = a .
eq state(switch(c2)) = a .
-- eq counter(c1) =*= counter(c2) = true .
eq read(counter(c1)) = read(counter(c2)) .

--> prove R is a congurence
--> following five reductions should be true
red put(n, c1) R put(n, c2) .
red add(c1) R add(c2) .
red sub(c1) R sub(c2) .
red counter(c1) =*= counter(c2) .
red switch(c1) =*= switch(c2) .
close

--> ---------------------------------------------------------------
--> sub put(m, add put(n, sub init)) R  put(n, sub put(m, add init))
--> ---------------------------------------------------------------
open CWS-PROOF
ops m n : -> Nat .
--> should be true
red sub(put(m, add(put(n, sub(init))))) R put(n, sub(put(m, add(init)))) .
close

open CWS-PROOF
ops m n : -> Nat .
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

open CWS-PROOF
op c : -> Cws .
op n : -> Int .
--> case 1: state(switch c) = on .
eq state(switch c) = on .

red read addc(n, c) == n + read c .
close

open CWS-PROOF
op c : -> Cws .
op n : -> Int .
--> case 2: state(switch c) = off .
eq state(switch c) = off .

red read addc(n, c) == n + read c .
close

--> prove that COUNTER-WITH-SWITCH refines SWITCH via \psi_1

open CWS-PROOF
op c : -> Cws .
op n : -> Int .

red state switch add(c) == on .
red state switch sub(c) == off .
close

--> prove the commutativity eqns corresponding to the methods

open CWS-PROOF
op c : -> Cws .
op n : -> Int .
--> case 1: state(switch c) = on .
eq state(switch c) = on .

red read add(addc(n, c)) == read addc(n, add(c)) .
red read sub(addc(n, c)) == read addc(n, sub(c)) .
close

open CWS-PROOF
op c : -> Cws .
op n : -> Int .
--> case 2: state(switch c) = off .
eq state(switch c) = off .

red read add(addc(n, c)) == read addc(n, add(c)) .
red read sub(addc(n, c)) == read addc(n, sub(c)) . 
close

--> prove the commutativity eqns corresponding to the attributes

open CWS-PROOF
op c : -> Cws .
op n : -> Int .

red state(switch put(n, c)) == state(switch c) .
red read(counter add(c)) == read(counter c) .
red read(counter sub(c)) == read(counter c) .
close




