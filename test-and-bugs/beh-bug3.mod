-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Mon, 27 Oct 97 17:30:20 JST
-- Message-Id: <9710270830.AA02291@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  some unexpected bug?
-- Content-Type: text
-- Content-Length: 1855

-- I have some troubles with a simple example which seemed to be working
-- well in previous versions. It is the "classical" stacks:

-- in simple-nat

-- call  "history sensitive storage"

mod* HSS(X :: TRIV) {

  *[ Hss ]*

  bop put : Elt Hss -> Hss
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Elt

  var S : Hss
  var E : Elt

  eq get put(E, S) = E .
  beq rest put(E, S) = S .
}

mod HSS-NAT-PROOF {
  protecting(HSS + BARE-NAT)

  bop rest* : Hss Nat -> Hss 

  vars S S1 S2 : Hss
  vars N N' : Nat
  var E : Elt

  eq  [ p1 ] : rest*(S, s(N)) = rest*(rest S, N) .
  eq  [ p2 ] : rest*(S, 0) = S .
}

open HSS-NAT-PROOF .

-- op _R_ : Hss Hss -> Bool .
-- S1 R S2 iff for all N \in Nat we have get rest*(S1, N) == get rest*(S2, N)

-- we prove that _R_ is a hidden congruence 

  ops m n : -> Nat .
  ops e e1 e2 : -> Elt .
  ops s s1 s2 : -> Hss .

  eq [ hyp ] : get rest*(s1, N) = get rest*(s2, N) .

-- -----
--> get |
-- -----
start get s1 == get s2 .
apply -.p2 within term .
apply .hyp within term .
apply reduce at term . -- it should be true


eof

This is the relevant sequence, and I get 

-- done reading in file: simple-nat
-- defining module* HSS_.*......._..*
* system failed to prove =*= is a congruence on hidden sort Hss.  done.
-- defining module HSS-NAT-PROOF_*.
[Warning]: behavioural operator "rest*" has imported hidden sort Hss in its arity....._..*
* system failed to prove =*= is a congruence on hidden sort Hss.  done.
-- opening module HSS-NAT-PROOF(X.HSS).. done._
--> get |*
* system failed to prove =*= is a congruence on hidden sort Hss. 
result get 
Error: Caught fatal error [memory may be damaged]
Fast links are on: do (si::use-fast-links nil) for debugging
Error signalled by CAFEOBJ-EVAL-APPLY-PROC.
Broken at EVAL-APPLY-COMMAND.  Type :H for Help.
CHAOS>>

Maybe this is again a mistake from me...?

Thanks,
Razvan
