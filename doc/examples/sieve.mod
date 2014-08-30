-- FILE: /home/diacon/LANG/Cafe/prog/sieve.mod
-- CONTENTS: equational program for computing prime numbers by
--           the Eratostene sieve algorithm featuring 
--           evaluation strategies and computation modulo axioms (A)
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

set tram path brute

mod! LAZYLIST (X :: TRIV ) {

    [ Elt < List ]

    op nil : -> List
    op __ : List List -> List {assoc idr: nil strat: (0)}
}

mod* INFLIST {
  protecting(LAZYLIST(INT))

  [ List < InfList ]

  op __ : List InfList -> InfList {strat: (0)}
  op ints-from_ : Int -> InfList 
  op show_upto_ : InfList Int -> List 
  op force : List InfList -> InfList {strat: (1 2 0)}
  
  vars E I : Int
  var L : List 
  var S : InfList

  eq force(L,S) = L S .
  eq show nil upto I = nil .
  eq show E S upto I = if I == 0 then nil
                                 else force(E,show S upto (I - 1)) fi . 
  eq ints-from I = I (ints-from (I + 1)) .
}

mod* SIEVE {
  protecting(INFLIST)

  op sieve_ : List -> List
  op sieve_ : InfList -> InfList
  op primes :  -> InfList 
  op filter_with_ : List Int -> List
  op filter_with_ : InfList Int -> InfList

  vars E I P : Int
  var S : InfList 

  eq filter nil with P = nil .
  eq filter I S with P = if (I rem P) == 0 then filter S with P
     else I (filter S with P) fi .
  eq sieve nil = nil .
  eq sieve (I S) = I (sieve (filter S with I)) .
  eq primes = sieve (ints-from 2) .
}

-- tram red in SIEVE : show primes upto 200 .
red in SIEVE : show primes upto 100 .

--
eof
--
$Id: sieve.mod,v 1.2 2010-06-17 08:23:18 sawada Exp $
