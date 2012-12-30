** -*- Mode:CafeOBJ -*-
** was combinators.obj(in OBJ3 distribution) translated to CafeOBJ.
--
module! COMBINATORS {
  -- protecting (CHAOS)  -- to import Identifier, should be used with care.
  signature {
    [ Identifier < T ]
    op __ : T T -> T {l-assoc strat: (1 2 0)}
    ops S K I : -> T
  }
  axioms {
    vars M N P : T 
    eq K M N = M .
    eq I M = M .
    eq S M N P = (M P) (N P).
  }
}

open COMBINATORS .
ops m n p : -> Identifier .
red S K K m == I m .
red S K S m == I m .
red S I I I m == I m .

red K m n == S(S(K S)(S(K K)K))(K(S K K)) m n .
--
red S m n p == S(S(K S)(S(K(S(K S)))(S(K(S(K K)))S)))(K(K(S K K))) m n p .
red S(K K) m n p == S(S(K S)(S(K K)(S(K S)K)))(K K) m n p .
--
close
--
eof
**
$Id: combinators.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
