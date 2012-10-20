-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Fri, 31 Oct 97 21:01:52 JST
-- Message-Id: <9710311201.AA03380@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  modularisation library in CafeOBJ
-- Cc: diacon@stoilow.imar.ro, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 5920

-- Dear Toshimi,

-- I have recently undertaken the task of seriously testing the module
-- system of CafeOBJ. I built a special library for this purpose, and I
-- tried to do something. Due to many errors I am thinking it would be
-- better to do it in a different way.

-- So, I am sending you the library and please tell me if you agree with
-- what is there and if my expectations are OK. Then after we agree on
-- the library please try to run it. Maybe many bugs will pop up and this
-- might help you stabilise the implementation of the module
-- system. Please keep in touch by saying sometimes what from this
-- library works and what we should expect to work in the future.

-- With many thanks,
-- Razvan

-- PS. This library will also be the example basis for the
-- modularisation chapter in the "CafeOBJ Report"
-- -----------------------------------------------------------------------
set auto context on

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! SIMPLE-NAT {
  protecting(BARE-NAT)

  -- op _+_ : Nat Nat -> Nat
  op _+_ : Nat Nat -> Nat { assoc }
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . eq 0 + N:Nat = N .
}

mod! TIMES-NAT {
  protecting(SIMPLE-NAT)

  -- op _*_ : Nat Nat -> Nat
  op _*_ : Nat Nat -> Nat { assoc }
  op _*_ : NzNat NzNat -> NzNat {assoc}
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
  [ Elt ]

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

view bare-nat from TRIV to BARE-NAT { sort Elt -> Nat }

-- _+_ of SIMPLE-NAT must have theory assoc.

view plus from MON to SIMPLE-NAT {
  sort Elt -> Nat, 
  op _;_ -> _+_,  
  op null -> 0 
}

-- _*_ of TIMES-NAT must have theory assoc

view times from MON to TIMES-NAT {
  sort Elt -> NzNat,
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
view times* from MON* to TIMES-NAT {
  sort Elt -> NzNat,
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
  op _^_ : Elt.M Elt.POWER -> Elt.M { assoc }

  vars m m' : Elt.M
  vars p p' :  Elt.POWER

  eq (m ; m')^ p   = (m ^ p) ; (m' ^ p) .
  eq  m ^ (p ; p') = (m ^ p) ; (m ^ p') .
  eq  m ^ null     =  null .
}

open MON-POW(plus,plus) * { op _^_ -> _*_ } .
  ops m m' n n' :  -> Nat .
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
red (m ; m') ^ (n + n') == (m ^ n) ; (m' ^ n) ; (m ^ n') ; (m' ^ n') .
close

-- this should be another version of TIMES-NAT
-- by getting the multiplication as power of the sum!
mod* NAT-TIMES {
  protecting(MON-POW-NAT(M <= plus) * { op _^_ -> _*_ })
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
  op _^_ : Elt.M Elt.POWER -> Elt.M {assoc}

  vars m m' : Elt.M
  vars p p' :  Elt.POWER

  eq (m ; m')^ p   = (m ^ p) ; (m' ^ p) .
  eq  m ^ (p ; p') = (m ^ p) ; (m ^ p') .
  eq  m ^ null     =  null .
}

mod* SRNG {
  protecting(CMON-POW * { sort Elt.POWER -> Srng,
			  sort Elt.M     -> Srng,
			  op (_;_)  -> _+_,
			  op null -> 0,
                          op _^_ -> _*_ })
}

open SRNG .
--   op m n m' n'  -> Srng .
  ops m n m' n' : -> Srng .
-- the following should be true
red (m + n) * (m' + n') == (m * n) + (m' * n) + (m * n') + (m' * n') .
close

-- ----------------------------------------------------------------
-- fully parameterised version of MONOIDS with POWERS
-- ----------------------------------------------------------------
mod* MON*-POW (POWER :: MON*, M :: MON*)
{
  op _^_ : Elt.M Elt.POWER -> Elt.M {assoc}

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
