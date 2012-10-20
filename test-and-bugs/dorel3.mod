-- Date: Mon, 29 Sep 1997 20:01:08 +0300 (EET DST)
-- From: Dorel Lucanu <dlucanu@thor.infoiasi.ro>
-- To: sawada@sra.co.jp
-- Subject: A bug?
-- Message-ID: <Pine.LNX.3.95.970929194743.23360B-100000@thor.infoiasi.ro>
-- MIME-Version: 1.0
-- Content-Type: TEXT/PLAIN; charset=US-ASCII
-- Content-Length: 4017

-- Dear Toshimi,

-- I try to design a fair VM based on pseudo-random numbers. But I failed to
-- run this example because the system produces an error. If my specification
-- is Ok then it seems to be a bug. I will be happy to know your opinion
-- about it. You find bellow my specifications and the response of the
-- system.

-- With best wishes,
-- Dorel.

-- P.S. Did you receive my previous message with a question on infinite
-- transitions?

-- *****************RAND.MOD****************
mod* RAND {
  protecting (NAT)
  *[ Rand ]*
  op init : -> Rand
  op next : Rand -> Rand
  op val : Rand -> Nat
  ops mult incr mod : -> Nat
  var R : Rand

  eq val(next(R)) = s((mult * val(R) + incr) quo mod) .
}

mod* RAND1 {
  extending (RAND * { hsort Rand -> Rand1,
                      op    init -> init1 })
  eq mult = 33 .
  eq mod = 512 .
  eq incr = 17 .

  eq val(init1) = 13 .
}

mod* RAND2 {
  extending (RAND * { hsort Rand -> Rand2,
                      op    init -> init2 })
  eq mult = 129 .
  eq mod = 1024 .
  eq incr = 61 .

  eq val(init2) = 13 .

}
-- *****************VM.MOD******************  
mod! DATA {
  [ Data ]
  ops coffee tea : -> Data
  op not_ : Data -> Data
  eq not coffee = tea .
  eq not tea = coffee .
}

mod* VM {
  protecting (DATA)
  *[ St ]*
  op init : -> St
  bop out : St -> Data 
  bop m : St -> St
}

mod FAIR-TEST (X :: VM) {
  protecting (X)
  protecting (NAT)
-- three new operations
  ops #coffee #tea : St -> Nat
  op  mm : St  Nat -> St
  var S : St
  var N : NzNat
-- definition of #coffee
  eq  #coffee(init) = 0 .
  ceq #coffee(m(S)) = #coffee(S) if out(m(S)) == tea .
  ceq #coffee(m(S)) = s #coffee(S) if out(m(S)) == coffee .
-- definition of #tea
  eq  #tea(init) = 0 .
  ceq #tea(m(S)) = #tea(S) if out(m(S)) == coffee .
  ceq #tea(m(S)) = s #tea(S) if out(m(S)) == tea .
-- definition of mm 
  eq mm(S,0) = S .
  eq mm(S, N) = m(mm(S, p N)) .
-- four lemmas
  ceq (#coffee(m(S)) > 0) = true if #coffee(S) > 0 .
  ceq (#tea(m(S)) > 0) = true if #tea(S) > 0 .
  ceq (#coffee(S) > 0) = true if out(S) == coffee .
  ceq (#tea(S) > 0) = true if out(S) == tea .
-- test for fairness property
-- (for all S:St there exists X:NzNat such that 
--          #coffee(mm(S,X)) > 0 and #tea(mm(S,X)) > 0 .
}
-- *******************RAND-VM.MOD**************
mod* RAND-VM {
  protecting (VM + RAND1 + RAND2)

  bops #av-tea #av-coffee : St -> Nat
  -- bop #in-coffee : -> Rand1
  -- bop #in-tea : -> Rand2
  bop #in-coffee : St -> Rand1
  bop #in-tea : St -> Rand2
  var S : St

  eq #in-coffee(init) = init1 .
  ceq #in-coffee(m(S)) = next(#in-coffee(S)) if #av-coffee(S) == 0 .

  eq #in-tea(init) = init2 .
  ceq #in-tea(m(S)) = next(#in-tea(S)) if #av-tea(S) == 0 .
  
  eq #av-coffee(init) = 0 .
  ceq #av-coffee(m(S)) =  #av-coffee(S) if out(m(S)) == tea .
  ceq #av-coffee(m(S)) =  p #av-coffee(S) if (out(m(S)) == coffee) and 
                                       (#av-coffee(S) > 0) .
  ceq #av-coffee(m(S)) =  val(#in-coffee(m(S))) if #av-coffee(S) == 0 .
  
  eq #av-tea(init) = 0 .
  ceq #av-tea(m(S)) =  #av-tea(S) if out(m(S)) == coffee .
  ceq #av-tea(m(S)) =  p #av-tea(S) if (out(m(S)) == tea) and 
                                       (#av-tea(S) > 0) .
  ceq #av-tea(m(S)) =  val(#in-tea(m(S))) if #av-tea(S) == 0 .
}
eof

-- *******************RESPONSE OF THE SYSTEM*****
-- processing input : ./rand.mod
-- defining module* RAND........._.* done.
-- defining module* RAND1,,,,,,,_,,*._....* done.
-- defining module* RAND2,,,,,,,_,,*._....* done.

CafeOBJ> in vm
-- processing input : ./vm.mod
-- defining module! DATA...._..* done.
-- defining module* VM....._*
* system failed to prove =*= is a congruence on hidden sort St.  done.
-- defining module FAIR-TEST_.*........_............* done.

CafeOBJ> in rand-vm
-- processing input : ./rand-vm.mod
-- defining module* RAND-VM
Error: The index, 6, is too large
Fast links are on: do (si::use-fast-links nil) for debugging
Error signalled by CAFEOBJ-EVAL-MODULE-PROC.
Broken at EVAL-IMPORT-MODEXP.  Type :H for Help.
CHAOS>>:q

CafeOBJ> q
[Leaving CafeOBJ]
****************************************
  
  


