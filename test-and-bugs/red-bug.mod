-- To: sawada@sra.co.jp
-- Subject:  bug(s) in new reduce
-- Cc: s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 6441
-- 
-- Dear Toshimi,
--
-- We just tried the new implementation of CafeOBJ (b10) on the CWS
-- example which should now work *without* any apply in the proof
-- scores.
-- 
-- Unfortunately we got false for all the interesting reductions! We did
-- some little investigations on this, and found out immediately two
-- places where things go wrong. Of course, there are many otehr places
-- too (for the other false). These two places feature 2 very different
-- troubles.
-- 
-- 1.

-- 1<[3] state (switch put(n,c1)) == state (switch put(n,c2)) --> false
-- 
-- Here the beq for switch put(n,c) should be used safely because of the
-- beh context with state at the top. Then it should give true.
-- 
-- 2.
-- 
-- 1>[7] apply trial #2
-- -- rule: bceq counter put(N:Nat,C:Cws) = add(N:Nat,counter C:Cws)
--         if state (switch C:Cws) == on
--     { N:Nat |-> n, C:Cws |-> c2 }
-- 2>[7] rule: eq state (switch c2) = on
--      {}
-- 2<[7] state (switch c2) --> on
-- 2>[8] rule: eq CXU == CYU = #!! (coerce-to-bool
--                                     (term-equational-equal cxu cyu))
--       { CXU |-> on, CYU |-> on }
-- 2<[8] on == on --> true
-- 1>[9] match success #2
-- 1<[9] counter put(n,c2) --> add(n,counter c2)
-- 1>[10] rule: eq hs1:Counter =*= hs2:Counter = read hs1:Counter ==
--        read hs2:Counter
--      { hs1:Counter |-> add(n,counter c1), hs2:Counter |-> add(n,counter
--          c2) }
-- 1<[10] add(n,counter c1) =*= add(n,counter c2) --> read add(n,counter
--      c1) == read add(n,counter c2)
--
--
-- Here some beq is applied violating the beh context condition. If step
-- [10] was applied BEFORE [7] then everythign would be OK becasue of the
-- read appearing and therefore there is a beh context with read as top
-- for safely applying the beq in [7]. Maybe this beh condition is not
-- working well for conditional beq?
-- 
-- This is all for the moment, we hope this will help you.
-- 
-- Best wishes,
-- Razvan & IIda-san
-- --------
-- PS. Here is the file we used.
--
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

eof
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
red put(n, c1) R put(n, c2) .
--> red add(c1) R add(c2) .
red  add(c1) R add(c2) .
--> red sub(c1) R sub(c2) .
red sub(c1) R sub(c2) .
--> red counter(c1) =*= counter(c2) .
red counter(c1) =*= counter(c2) .
--> red switch(c1) =*= switch(c2) .
red switch(c1) =*= switch(c2) .
close

--> ---------------------------------------------------------------
--> sub put(m, add put(n, sub init)) R  put(n, sub put(m, addinit))
--> ---------------------------------------------------------------
open CWS-PROOF
ops m n : -> Nat .
--> should be true
--> red sub(put(m, add(put(n, sub(init))))) R put(n, sub(put(m, add(init)))) .
red sub(put(m, add(put(n, sub(init))))) R put(n, sub(put(m, add(init)))) .
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




