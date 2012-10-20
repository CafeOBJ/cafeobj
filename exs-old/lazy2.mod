** -*- Mode:CafeOBJ -*-

module! LAZYCONS ( X :: TRIV )
{
  signature {
    [ Elt, List ]
    op nil : -> List { constr }
    op cons : Elt List -> List { constr strat: (0) }
    op car : List -> Elt {strategy: (1 0)}
    op cdr : List -> List {strategy: (1 0)}
  }
  axioms {
    eq car(cons(X:Elt, Y:List)) = X .
    eq cdr(cons(X:Elt, Y:List)) = Y .
  }
}
  
module! SIEVE'
{
  protecting (LAZYCONS[ X <= INT ])
  -- 
  signature {  
    op force : Int List -> List { strat: (1 2 0) }
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
    eq force(I,S) = cons(I, S) .
    eq show nil upto I = nil .
    eq show cons(E, S) upto I
       = if I == 0 then nil
                   else force(E, show S upto (I - 1)) fi .
    eq filter nil with P = nil .
    eq filter cons(I, S) with P
       = if (I rem P) == 0 then filter S with P 
                           else cons(I, (filter S with P)) fi .
    eq ints-from I = cons(I, (ints-from (I + 1))) .
    eq sieve nil = nil .
    eq sieve cons(I, S) = cons(I, (sieve (filter S with I))) .
    eq primes = sieve (ints-from 2) .
  }
}

red in SIEVE' : show primes upto 10 .
eof
**
$Id: lazy2.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $

