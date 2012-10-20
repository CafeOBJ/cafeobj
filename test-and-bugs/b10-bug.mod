-- Date: Thu, 14 Aug 97 17:39:19 JST
-- Message-Id: <9708140839.AA02399@is27e0s07.jaist.ac.jp>
-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Cc: s_iida@jaist.ac.jp
-- Subject: bug in b10
-- Content-Type: text
-- Content-Length: 6795

-- Dear Toshimi,

-- Thanks a lot for your feedback on the CafeOBJ Report examples! 

-- I have just tried version b10 on the CWS example and I think there is
-- a bug which prevents this example for running. 

-- I get the following:

-- -- CafeOBJ> in cws
-- -- processing input : ./cws.mod
-- --> THE "APPLY" PROOF SCORES SHOULD BE REVERSED TO PURE "REDUCE"
-- --> PROOF SCORES ONCE THE BEH CONTEXT CONDITION IS IMPLEMENTED
-- -- defining module! ON-OFF
-- [Warning]: redefining module ON-OFF ..._* done.
-- -- defining module* SWITCH
-- [Warning]: redefining module SWITCH ......._...*
-- * system already proved =*= is a congruence on hidden sort Switch.  done.
-- -- defining module* COUNTER
-- [Warning]: redefining module COUNTER ......._..*
-- * system already proved =*= is a congruence on hidden sort Counter.  done.
-- -- defining module* COUNTER-WITH-SWITCH
-- [Warning]: redefining module COUNTER-WITH-SWITCH _*..........._.
-- [Error]: behavioural axiom must be constructed from terms of behavioural operators.*
-- -- failed to evaluate the form:
-- axiom declaration(equation): 
--  lhs = (switch ( init ))
--  rhs = (init)

-- ** returning to top level

-- CafeOBJ>

-- I made some tests and it seems it is because of 

-- rhs = (init)

-- Maybe it is because the system "forgets" that constants (even if
-- declared with op) are still OK for behavioural sentences. Also notice
-- that the corrersponding error is not very well formulated. Maybe it
-- will be better to say something like

-- [Error]: behavioural axiom must not contain operators on hidden sorts
-- (other than constants) which are not behavioural

-- Please let me know if I am confused and I did some silly mistake. 

-- After this message I insert the cws.mod file. 

-- Best wishes,
-- Razvan
-- ----------------------------------------------------------------------
--> THE "APPLY" PROOF SCORES SHOULD BE REVERSED TO PURE "REDUCE"
--> PROOF SCORES ONCE THE BEH CONTEXT CONDITION IS IMPLEMENTED

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
  bop put : Nat Cws -> Cws            -- method
  bop add_ : Cws -> Cws                -- method
  bop sub_ : Cws -> Cws                -- method
  bop read_ : Cws -> Int               -- attribute 
  bop counter_ : Cws -> Counter    -- projection function
  bop switch_ : Cws -> Switch      -- projection function

  var N : Nat
  var C : Cws

  eq read C = read(counter C) .  -- abbreviation equation for "read"

-- -------------------------------------
-- behavioural equations for switch
-- -------------------------------------
  beq switch init = init .
  beq switch put(N, C) = switch C .
  beq switch add(C) = on(switch C) .
  beq switch sub(C) = off(switch C) .

-- -------------------------------------
-- behavioural equations for counter
-- -------------------------------------
  beq counter init = init .
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

-- R is a hidden equivalence relation
  op _R_ : Cws Cws -> Bool

  vars C1 C2 : Cws

  eq C1 R C2 =  switch(C1) =*= switch(C2) and
               counter(C1) =*= counter(C2) .
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
--> red put(n, c1) R put(n, c2) .
start put(n, c1) R put(n, c2) .
apply .1 at term .
apply +SWITCH.5 within term .
apply +COUNTER.4 within term .
apply reduce at term .
--> red add(c1) R add(c2) .
start add(c1) R add(c2) .
apply .1 at term .
apply +SWITCH.5 within term .
apply +COUNTER.4 within term .
apply reduce at term .
--> red sub(c1) R sub(c2) .
start sub(c1) R sub(c2) .
apply .1 at term .
apply +SWITCH.5 within term .
apply +COUNTER.4 within term .
apply reduce at term .

red counter(c1) =*= counter(c2) .
red switch(c1) =*= switch(c2) .
close

--> ---------------------------------------------------------------
--> sub put(m, add put(n, sub init)) R  put(n, sub put(m, addinit))
--> ---------------------------------------------------------------
open CWS-PROOF
ops m n : -> Nat .
--> should be true
--> red sub(put(m, add(put(n, sub(init))))) R put(n, sub(put(m, add(init)))) .
start sub(put(m, add(put(n, sub(init))))) R put(n, sub(put(m, add(init)))) .
apply .1 within term .
apply +SWITCH.5 within term .
apply +COUNTER.4 within term .
apply reduce at term .
close

--> ---------------------------------------------------------------------
--> read put(m, add put(n, sub init)) == read put(n, sub put(m, add init))
--> ---------------------------------------------------------------------
open CWS-PROOF
ops m n : -> Nat .
--> should be true
red read(put(m, add(put(n, sub(init))))) ==
    read(put(n, sub(put(m, add(init))))) .
close


eof
