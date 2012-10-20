** -*- Mode:CafeOBJ -*-

** ===================================================================
-- SIEVE : a prime number seive.
-- -------------------------------------------------------------------

module* LAZYLIST (X :: TRIV )
{
  signature {
    [ Elt < List ]
    op nil : -> List
    op __ : List List -> List { assoc idr: nil strat: (0) }
  }
}
  
module! SIEVE
{
  protecting (LAZYLIST[INT])	-- NOTE: builtin INT declares Int as its 
				-- principal sort.
  -- 
  signature {  
    op force : List List -> List { strat: (1 2 0) }
    op show_upto_ : List Int -> List 
    op filter_with_ : List Int -> List
    op ints-from_ : Int -> List { prec: 51 }
    op sieve_ : List -> List 
    op primes : -> List
  }
  -- 
  axioms {
    var P : NzInt
    vars I E : Int
    vars L S : List
    eq force(L,S) = L S .
    eq show nil upto I = nil .
    eq show E S upto I = if I == 0 then nil
                         else force(E, show S upto (I - 1)) fi .
    eq filter nil with P = nil .
    eq filter I S with P = if (I rem P) == 0 then filter S with P 
                           else I (filter S with P) fi .
    eq ints-from I = I (ints-from (I + 1)) .
    eq sieve nil = nil .
    eq sieve (I S) = I (sieve (filter S with I)) .
    eq primes = sieve (ints-from 2) .
  }
}

-- red in SIEVE : show primes upto 10 .
--
eof
--
$Id: sieve.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $

