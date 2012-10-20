set auto context on .
-- example of concurrent object composition in behavioural specification
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

  eq switch(init) = init .
  eq switch put(N, C) = switch C .
  eq switch add(C) = on(switch C) .
  eq switch sub(C) = off(switch C) .

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
  protecting(COUNTER-WITH-SWITCH)

-- R is a hidden equivalence relation
  op _R_ : Cws Cws -> Bool   { coherent }
  vars C1 C2 : Cws

  eq C1 R C2 = state(switch(C1)) == state(switch(C2)) and
               read(counter(C1)) == read(counter(C2)) .

  ops m n : -> Nat
}

--> ---------------------------------------------------------------
--> sub put(m, add put(n, sub init)) R  put(n, sub put(m, add init))
--> ---------------------------------------------------------------
set tram path brute .
--> should be true
set trace on .
tram red sub(put(m, add(put(n, sub(init))))) R put(n, sub(put(m, add(init)))) .
set trace off .