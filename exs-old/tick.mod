** -*- Mode:CafeOBJ -*-

** ==================================================================
-- An Example of object.
** ==================================================================

module! CLOCK {
 protecting (ACZ-CONFIGURATION)
 protecting (NAT)

 signature {
   -- Class Clock
   class Clock { time : Nat }
   op tick : ObjectId -> Message
  }
  axioms {
    -- rule -------------
    var O : ObjectId
    var N : Nat
    trans [ tick ]: tick(O) < O : Clock | time = N > 
      => < O : Clock | time = (N + 1) > tick(O) .
  }
}

**> try the followings.
--> select CLOCK
--> exec delete < Clock1 : Clock > .
--> exec makeClock(Clock1, (time = 0)) .
--> set rwt limit 100 
--> exec tick(Clock1) < Clock1 : Clock > .
--> reduce < Clock1 : Clock > .
--
eof
--
$Id: tick.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
