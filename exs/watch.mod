-- FILE: /home/diacon/LANG/Cafe/prog/watch.mod
-- CONTENTS: behavioural specification of a watch objcet as concurrent
--           composition with synchronization of 3 objects
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

-- set tram path brute

-- natural numbers with an arbitrary constant
mod* NATn {
  protecting(NAT)
  op n :  -> NzNat 
}

-- generic tick object
mod* INCn(X :: NATn) {

  *[ Value ]*

  op init :  -> Value 
  bop val : Value -> Nat 
  bop inc_ : Value -> Value 

  var T : Value

  eq val(inc T) = (val(T) + 1) rem n .
  eq val(init) = 0 .
}

-- the second watch object
mod* SEC {
  protecting(INCn(X <= view to NAT { op n -> 60 }) *{ hsort Value -> Sec })
}
-- the minute watch object
mod* MIN {
  protecting(INCn(X <= view to NAT { op n -> 60 }) *{ hsort Value -> Min })
}
-- the hour watch object
mod* HOUR {
  protecting(INCn(X <= view to NAT { op n -> 24 }) *{ hsort Value -> Hour })
}

-- the composed watch object
mod* WATCH {
  protecting (SEC + MIN + HOUR)
  protecting (3TUPLE(NAT,NAT,NAT)
	      *{ sort 3Tuple -> TIME,
		 op <<_;_;_>> -> _:_:_ })
  
  *[ Watch ]*

  bop sec :  Watch -> Sec  {memo}  -- projection
  bop min :  Watch -> Min  {memo}  -- projection
  bop hour : Watch -> Hour {memo}  -- projection

  op init : -> Watch
  bop tick : Watch -> Watch

  bop SEC : Watch -> Nat   
  bop MIN : Watch -> Nat   
  bop HOUR : Watch -> Nat  
  bop TIME : Watch -> TIME -- derived attribute

  var W : Watch

  eq sec(init) = init .
  eq min(init) = init .
  eq hour(init) = init .

  eq SEC(W) = val(sec(W)) .
  eq MIN(W) = val(min(W)) .
  eq HOUR(W) = val(hour(W)) .
  eq TIME(W) = HOUR(W) : MIN(W) : SEC(W) .
  		   
  eq sec(tick(W)) = inc sec(W) .
  ceq min(tick(W)) = min(W)        if SEC(tick(W)) =/= 0 .
  ceq min(tick(W)) = inc min(W)   if SEC(tick(W))  == 0 .
  ceq hour(tick(W)) = hour(W)
      if (MIN(tick(W)) =/= 0) or (SEC(tick(W)) =/= 0) .
  ceq hour(tick(W)) = inc hour(W) 
      if (MIN(tick(W))  == 0) and (SEC(tick(W)) == 0) .
}

-- some testing
open WATCH .
  op watch : -> Watch .
--> TIME is 23 : 59 : 59
  eq val(sec(watch)) = 59 .
  eq val(min(watch)) = 59 .
  eq val(hour(watch)) = 23 .
--> after 2 ticks... 
red TIME(tick(tick(watch))) .
close

-- more complex watch inheriting the simpler one 
mod* CWATCH {
  protecting(WATCH)

  *[ CWatch < Watch ]*

  op init : -> CWatch
  bop tick : CWatch -> CWatch

  bop inc-sec : CWatch -> CWatch 
  bop inc-min : CWatch -> CWatch
  bop inc-hour : CWatch -> CWatch

  var W : CWatch 

  beq inc-sec(W) = tick(W) .
  eq sec(inc-min(W)) = sec(W) .
  eq min(inc-min(W)) = inc min(W) .
  ceq hour(inc-min(W)) = hour(W)        if MIN(inc-min(W)) =/= 0 .
  ceq hour(inc-min(W)) = inc hour(W)   if MIN(inc-min(W))  == 0 .

  eq sec(inc-hour(W)) = sec(W) .
  eq min(inc-hour(W)) = min(W) .
  eq hour(inc-hour(W)) = inc hour(W) .
}

-- some testing
open CWATCH .
op watch : -> CWatch .
--> TIME is 23 : 59 : 59
  eq val(sec(watch)) = 59 .
  eq val(min(watch)) = 59 .
  eq val(hour(watch)) = 23 .
--> set the watch forward by 1 minute and 1 second... 
red TIME(inc-min(inc-sec(watch))) .
close

mod WATCH-BEQ {
  protecting (CWATCH)

  op _R_ : CWatch CWatch -> Bool {coherent}

  vars W W' : CWatch

  eq W R W' = sec(W) =*= sec(W') and
              min(W) =*= min(W') and
              hour(W) =*= hour(W') . 
}

-- proof of true concurrency of tick and inc-min methods
mod PROOF {
  protecting (WATCH-BEQ + INT)

  op w : Nat Nat Nat  -> CWatch 

  vars S M H N : Nat 

  eq val(sec(w(S,M,H))) = S .
  eq val(min(w(S,M,H))) = M .
  eq val(hour(w(S,M,H))) = H .

-- the generic proof term
  op TERM : Nat Nat Nat -> Bool
  eq TERM(S,M,H) = inc-min(tick(w(S,M,H))) R tick(inc-min(w(S,M,H))) .
-- generation of whole case analysis
  op TERM1 : Nat Nat Nat -> Bool
  ceq TERM1(S,M,H) = TERM(S,M,H) and TERM1(S - 1,M,H) if 0 < S .
  eq TERM1(0,M,H) = TERM(0,M,H) .

  op TERM2 : Nat Nat -> Bool
  eq TERM2(M,H) = TERM1(59,M,H) .

  op TERM3 : Nat Nat -> Bool
  eq TERM3(0,H) = TERM2(0,H) .
  cq TERM3(M,H) = TERM2(M,H) and TERM3(M - 1,H)  if 0 < M .

  op TERM4 : Nat -> Bool
  eq TERM4(H) = TERM3(59,H) .

  op TERM5 : Nat -> Bool
  eq TERM5(0) = TERM4(0) .
  cq TERM5(H) = TERM4(H) and TERM5(H - 1) if 0 < H .

  op RESULT :  -> Bool
  eq RESULT = TERM5(23) .
}

-- tram red in PROOF : RESULT .
--> this reduction requres much time to perform, please be patient.
reduce in PROOF : RESULT .
--
eof
--
$Id: watch.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
