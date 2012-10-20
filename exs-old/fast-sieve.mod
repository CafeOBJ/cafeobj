-- -*- Mode:CafeOBJ -*-
** ===================================================================
-- SIEVE : a prime number seive. 
-- faster than sieve.mod
-- -------------------------------------------------------------------

module! LAZYLIST2 ( X :: TRIV )
{
  signature {
    [ Elt, List ]
    op nil : -> List { constr }
    op lcons : Elt List -> List { constr strat: (0) }
  }
}
  
module! SIEVE2
{
  protecting (LAZYLIST2[ X <= NAT ])
  -- 
  signature {  
    op force : Nat List -> List { strat: (1 2 0) }
    op show_upto_ : List Nat -> List 
    op filter_with_ : List Nat -> List
    op ints-from_ : Nat -> List { prec: 51 }
    op sieve_ : List -> List 
    op primes : -> List
  }
  -- 
  axioms {
    var P : NzNat
    vars I E : Nat
    vars L S : List
    eq force(E,S) = lcons(E, S) .
    eq show nil upto I = nil .
    eq show lcons(E, S) upto I
       = if I == 0 then nil
                   else force(E, show S upto (p I)) fi .
    eq filter nil with P = nil .
    eq filter lcons(I, S) with P
       = if (I rem P) == 0 then filter S with P 
                           else lcons(I, (filter S with P)) fi .
    eq ints-from I = lcons(I, (ints-from (s I))) .
    eq sieve nil = nil .
    eq sieve lcons(I, S) = lcons(I, (sieve (filter S with I))) .
    eq primes = sieve (ints-from 2) .
  }
}

red in SIEVE2 : show primes upto 10 .
eof
**
$Id: fast-sieve.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
