mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s : Nat -> NzNat
}

mod! SIMPLE-NAT {
  protecting (BARE-NAT)

  op _+_ : Nat Nat -> Nat 
  
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . eq 0 + N:Nat = N .
}

mod! TIMES-NAT {
  protecting (SIMPLE-NAT)

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

  op null :  ->  Elt
  op _;_ : Elt Elt -> Elt {assoc idr: null} 
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
-- LEMMA:
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
}

open NAT-TIMES .
-- LEMMA:
 eq M:Nat * s(N:Nat) = (M * N) + M .

red s(s(s(0))) * s(s(s(s(0)))) . -- it should be 12
close

view nat-times from MON to NAT-TIMES {
  sort Elt -> Nat,
  op null -> s(0),
  op _;_ -> _*_
}

mod* NAT-POW {
  protecting(MON-POW-NAT(M <= nat-times))
}

open NAT-POW .
-- LEMMA:
  eq M:Nat * s(N:Nat) = (M * N) + M . -- (1)
-- LEMMA:
  eq M:Nat ^ s(N:Nat) = (M ^ N) * M . -- (2)

red s(s(s(0))) ^ s(s(s(s(0)))) . -- it should be 81
close
       
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

module* SRNG
{
  protecting (CMON-POW(MON, CMON) *
		{ sort Elt -> Srng,
		  op (_;_) -> _+_,
		  op null -> 0,
		  op _^_ -> _*_ }
	      )
}

open SRNG .
  ops m n m' n'  : -> Srng .
-- the following should be true
red (m + n) * (m' + n') == (n * n') + (n * m') + (m * n') + (m * m') .
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

** describe MON*-POW(POWER <= plus*, M <= dual*)

open MON*-POW(plus*,plus*) * { op _^_ -> _*_ } .
  ops m m' n n' :  -> Nat .
** we need associativity and commutativity of _+_ here
  op _+_ : Nat Nat -> Nat { assoc comm }
-- the following should be true
red (m + m') * (n + n') == (m * n) + (m * n') + (m' * n) + (m' * n') .
close

-- ------------------------------------------------------------
-- ------------------------------------------------------------
--> proof that *dual* is indeed a specification morphism
mod* MONOID (X :: MON) { }

open MONOID(dual) .
  ops x y z :  -> Elt .
  op _|_ : Elt Elt -> Elt . 
  eq X:Elt | Y:Elt = Y ; X .

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
  vars X Y Z : Int .
  op _;_ : Int Int -> Int . 
  eq X ; Y = X + Y - X * Y .
-- lemmas:
  op _+_ : Int Int -> Int {assoc comm idr: 0}
  op _*_ : Int Int -> Int {assoc comm idr: 1}
  eq X + 0 = X .
  eq X * 0 = 0 .
  eq X * (Y + Z) = (X * Y) + (X * Z) .
  eq X * (- Y) = - (X * Y) .
  eq - - X = X .
  eq - (X + Y) = (- X) + (- Y) .
-- proof
red (x ; y) ; z == x ; (y ; z) .
red x ; 0 == x .
red 0 ; x == x .
close
--
eof
--
$Id: monoid.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
