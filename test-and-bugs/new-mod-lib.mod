-- Return-Path: diacon@jaist.ac.jp 
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id OAA19003 for <sawada@sras75.sra.co.jp>; Tue, 4 Nov 1997 14:14:25 +0900
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id OAA25336
-- 	for <sawada@srasva.sra.co.jp>; Tue, 4 Nov 1997 14:13:31 +0900 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id OAA20881
-- 	for <sawada@sra.co.jp>; Tue, 4 Nov 1997 14:10:43 +0900 (JST)
-- Received: from mikan.jaist.ac.jp ([150.65.8.6])
-- 	by sraigw.sra.co.jp (8.8.7/3.6Wbeta7-sraigw) with ESMTP id OAA03774
-- 	for <sawada@sra.co.jp>; Tue, 4 Nov 1997 14:14:49 +0859 (JST)
-- Received: from is27e0s07.jaist.ac.jp (Razvan Diaconescu <diacon@jaist.ac.jp>) by mikan.jaist.ac.jp (8.7.5); id OAA21082; Tue, 4 Nov 1997 14:15:02 +0900 (JST)
-- Received: by is27e0s07.jaist.ac.jp (4.1/JE-C); Tue, 4 Nov 97 14:15:00 JST
-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Tue, 4 Nov 97 14:15:00 JST
-- Message-Id: <9711040515.AA03960@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  new version of monoids library
-- Content-Type: text
-- Content-Length: 5426

-- Toshimi,

-- I just made some small changes in our modularisation library. After
-- thinking carefully I think we should stick with the strict definition
-- of views and do the overloading only at the level of
-- specifications. Secondly I changed  (m ^ n) ; (m' ^ n) ; (m ^ n') ; (m' ^ n')
-- to (m ^ n) ; (m ^ n') ; (m' ^ n) ; (m' ^ n') in the testing of
-- MON-POW-NAT.

-- Razvan
-- ---------------------------------------------------------------------
set auto context on

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! SIMPLE-NAT {
  protecting(BARE-NAT)

  op _+_ : Nat Nat -> Nat 
  
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . eq 0 + N:Nat = N .
}

mod! TIMES-NAT {
  protecting(SIMPLE-NAT)

  op _*_ : Nat Nat -> Nat

  vars M N : Nat 
    
  eq 0 * N = 0 .
  eq N * 0 = 0 .
  eq N * s(M) = (N * M) + N .
}

-- --------------------------------------------
-- MONOIDS
-- --------------------------------------------     
mod* MON {
  [ Elt ]

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

mod* CMON {
  protecting(MON)

  op _;_ : Elt Elt -> Elt {comm}
}

view bare-nat from TRIV to BARE-NAT { sort Elt -> Nat }

view plus from MON to SIMPLE-NAT {
  sort Elt -> Nat, 
  op _;_ -> _+_,  
  op null -> 0 
}
view times from MON to TIMES-NAT {
  sort Elt -> Nat,
  op _;_ -> _*_,
  op null -> s(0)
}
view dual from MON to MON {
  op X:Elt ; Y:Elt -> Y:Elt ; X:Elt 
}

mod* MON* (Y :: TRIV) {
  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

view dual* from MON* to MON* {
  op X:Elt ; Y:Elt -> Y:Elt ; X:Elt 
}
view plus* from MON* to SIMPLE-NAT {
  sort Elt -> Nat, 
  op _;_ -> _+_,  
  op null -> 0 
}
-- sort Elt -> NzNat,
view times* from MON* to TIMES-NAT {
  sort Elt -> Nat,
  op _;_ -> _*_,
  op null -> s(0)
}
view bnat+ from MON*(bare-nat) to SIMPLE-NAT {
  op _;_ -> _+_,
  op null -> 0
}    

-- -----------------------------------------------------------------
-- MONOIDS with POWERS
-- -----------------------------------------------------------------
mod* MON-POW (POWER :: MON, M :: MON)
{
  op _^_ : Elt.M Elt.POWER -> Elt.M

  vars m m' : Elt.M
  vars p p' :  Elt.POWER

  eq (m ; m')^ p   = (m ^ p) ; (m' ^ p) .
  eq  m ^ (p ; p') = (m ^ p) ; (m ^ p') .
  eq  m ^ null     =  null .
}

open MON-POW(plus,plus) * { op _^_ -> _*_ } .
  ops m m' n n' :  -> Nat .
-- _+_ must be associative, we should prove it of course!!
  op _+_ : Nat Nat -> Nat { assoc }
-- the following should be true
red (m + m') * (n + n') == (m * n) + (m * n') + (m' * n) + (m' * n') .
close

view ^as* from MON-POW(plus,plus) to TIMES-NAT {
  op _^_ -> _*_ 
}

mod* NAT^ (M :: MON-POW(plus,plus)) { }

open NAT^(^as*) .
red s(s(s(0))) * s(s(s(s(0)))) . -- it should be 12
close

mod* MON-POW-NAT {
  protecting(MON-POW(POWER <= plus))

  eq m:Elt.M ^ s(0) = m . 
}

open MON-POW-NAT .
  ops m m' :  -> Elt.M .
  ops n n' :  -> Nat .
-- this should be true
red (m ; m') ^ (n + n') == (m ^ n) ; (m ^ n') ; (m' ^ n) ; (m' ^ n') .

close

-- this should be another version of TIMES-NAT
-- by getting the multiplication as power of the sum!
mod* NAT-TIMES {
  protecting(MON-POW-NAT(M <= plus) * { op _^_ -> _*_ })
  eq M:Nat * s(N:Nat) = (M * N) + M . -- (1)
}

red s(s(s(0))) * s(s(s(s(0)))) . -- it should be 12

view nat-times from MON to NAT-TIMES {
  sort Elt -> Nat,
  op null -> s(0),
  op _;_ -> _*_
}

mod* NAT-POW {
  protecting(MON-POW-NAT(M <= nat-times))
}

-- red s(s(s(0)) ^ s(s(s(s(0)))) . -- it should be 81
red s(s(s(0))) ^ s(s(s(s(0)))) . -- it should be 81
       
-- ----------------------------------------------
-- SEMIRINGS
-- ----------------------------------------------

-- commutative monoids with powers
mod* CMON-POW (POWER :: MON, M :: CMON)
{
  op _^_ : Elt.M Elt.POWER -> Elt.M

  vars m m' : Elt.M
  vars p p' :  Elt.POWER

  eq (m ; m')^ p   = (m ^ p) ; (m' ^ p) .
  eq  m ^ (p ; p') = (m ^ p) ; (m ^ p') .
  eq  m ^ null     =  null .
}

-- mod* SRNG {
--   protecting(CMON-POW * { sort Elt.POWER -> Srng,
-- 			  sort Elt.M     -> Srng,
-- 			  op (_;_)  -> _+_,
-- 			  op null -> 0,
--                           op _^_ -> _*_ })
-- }

-- open SRNG .
--   ** op m n m' n'  -> Srng .
--   ops m n m' n' : -> Srng .
-- -- the following should be true
-- red (m + n) * (m' + n') == (m * n) + (m' * n) + (m * n') + (m' * n') .
-- close

module* SRNG
{
  protecting (CMON-POW(CMON, CMON) *
		{ sort Elt -> Srng,
		  op (_;_) -> _+_,
		  op null -> 0,
		  op _^_ -> _*_ }
	      )
}

open SRNG .
   ** op m n m' n'  -> Srng .
   ops m n m' n' : -> Srng .
-- the following should be true
-- red (m + n) * (m' + n') == (m * n) + (m' * n) + (m * n') + (m' * n') .
-- the above should be something like ...
red (m + n) * (m' + n') == (m * n') + (n * n') + (m * m') + (n * m') .
close

-- ----------------------------------------------------------------
-- full parameterised version of MONOIDS with POWERS
-- ----------------------------------------------------------------
mod* MON*-POW (POWER :: MON*, M :: MON*)
{
  op _^_ : Elt.M Elt.POWER -> Elt.M

  vars m m' : Elt.M
  vars p p' :  Elt.POWER

  eq (m ; m')^ p   = (m ^ p) ; (m' ^ p) .
  eq  m ^ (p ; p') = (m ^ p) ; (m ^ p') .
  eq  m ^ null     =  null .
}

describe MON*-POW(POWER <= plus*, M <= dual*)

open MON*-POW(plus*,plus*) * { op _^_ -> _*_ } .
  ops m m' n n' :  -> Nat .
-- the following should be true
red (m + m') * (n + n') == (m * n) + (m * n') + (m' * n) + (m' * n') .
close

-- ------------------------------------------------------------
-- ------------------------------------------------------------
--> proof that *dual* is indeed a specification morphism
open MONOID(dual) * { op _;_ -> _|_ } .
  ops x y z :  -> Elt .
parse x | y . 
red (x | y) | z == x | (y | z) .
red x | null == x .
red null | x == x .
close

view star from MON to INT {
  sort Elt -> Int,
  op null -> 0,
  op X:Elt ; Y:Elt -> X:Int + Y:Int - X * Y
}

--> proof that *star* is indeed a specification morphism
open MONOID(star) .
  ops x y z :  -> Int .
red (x ; y) ; z == x ; (y ; z) .
red x ; 0 == 0 .
red 0 ; x == 0 .
close
