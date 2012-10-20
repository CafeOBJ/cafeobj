-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sun, 3 May 98 19:13:33 JST
-- Message-Id: <9805031013.AA04582@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  another bug
-- Content-Type: text
-- Content-Length: 1410

-- Dear Toshimi,

-- Here is maybe another bug, when loading a file it gives stack
-- overflow!

mod! UBUF(X :: TRIV) {

  *[ UBuf ]*

  op init :  -> UBuf
  bop put : UBuf Elt -> UBuf 
  bop get_ : UBuf -> Elt
  bop empty? : UBuf -> Bool

  var UB : UBuf
  var E : Elt

  eq empty?(init) = true .
  cq get put(UB, E) = E      if not empty?(put(UB, E)) .
}

mod* DUBUF(X :: TRIV) {
  protecting(UBUF(X))

  bop put*_ : UBuf -> UBuf
  bop put! : UBuf Elt -> UBuf

  var UB : UBuf
  var E : Elt

  cq put(UB, E) = put* UB      if empty?(put(UB, E)) .
  eq put* put* UB = put* UB .
  eq empty?(put* UB) = true .
    
  cq put!(UB, E) = put(UB, E)           if not empty?(put(UB, E)) .
  cq put!(UB, E) = put!(put(UB, E), E)      if empty?(put(UB, E)) .
}

eof

-- UBUF(X)> in ubuffer
-- processing input : ./ubuffer.mod
-- -- defining module! UBUF
-- [Warning]: redefining module UBUF _*_*........_..*
-- ** system failed to prove =*= is a congruence of UBUF done.
-- -- defining module* DUBUF
-- [Warning]: redefining module DUBUF _*_*.,,,,,,,,*.
-- [Warning]: behavioural operator "put*_" has imported hidden sort UBuf in its arity..
-- [Warning]: behavioural operator "put!" has imported hidden sort UBuf in its arity...._.....*
-- Error: Caught fatal error [memory may be damaged]
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by CAFEOBJ-EVAL-MODULE-PROC.
-- Broken at DECLARE-MODULE.  Type :H for Help.
-- CHAOS>>


--
Razvan


