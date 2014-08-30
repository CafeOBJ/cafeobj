-- FILE: /home/diacon/LANG/Cafe/prog/sorting.mod
-- CONTENTS: generic sorting algorithm for strings featuring
--             algorithm execution modulo axioms
--             reasoning about the algorithm in RWL
--             module parameterization mechanism
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ****

-- generic strings
mod! STRG (X :: TRIV) {
  [ Elt < Strg ]

  op nil :  -> Elt 
  op __ : Strg Strg -> Strg {assoc idr: nil} 
}

-- the theory of partially ordered sets
mod* POSET {
  [ Elt ]

  op _<=_ : Elt Elt -> Bool 

  vars E1 E2 E3 : Elt

  eq E1 <= E1 = true .
  cq [:non-exec]: E1 = E2  if (E1 <= E2) and (E2 <= E1) .
  cq [:non-exec]: (E1 <= E3) = true      if (E1 <= E2) and (E2 <= E3) .
}

-- generic sorting algorithm
mod! SORTING-STRG(Y :: POSET) {
  protecting(STRG(Y))
  
  ctrans N:Elt N':Elt => N' N  if (N' <= N) and (N =/= N') .
}

** set exec normalize on <- now this is an obsolete switch.

open SORTING-STRG(NAT) .
exec (4 3 5 3 1) .
-- fast execution by brute engine
-- set tram path brute .
-- tram exec (40  39  38  37  36  35  34  33  32  31  30  29  28  27  26  25  24  23  22  21  20  19  18  17  16  15  14  13  12  11  10  9  8  7  6  5  4  3  2  1) .
close

-- functions for proving the generic termination of the sorting algorithm
mod! SORTING-STRG-PROOF {
  protecting(SORTING-STRG + NAT)
  
  op disorder : Strg -> Nat 
  op _>>_ : Elt Strg -> Nat

  vars E E' : Elt 
  var S : Strg 
    
  eq disorder(nil) = 0 .
  eq disorder(E) = 0 .
  eq disorder(E S) = disorder(S) + (E >> S) .

  eq E >> nil = 0 .
  cq E >> E' = 0 if E <= E' .
  cq E >> E' = 1 if (E' <= E) and (E =/= E')  .
  cq E >> (E' S) = s(E >> S) if (E' <=  E) and (E =/= E') .
  cq E >> (E' S) = (E >> S)  if E <= E' .
}

**> THEOREM: the sorting always terminates
**> s ==> s' implies disorder(s') < disorder(s)

**> LEMMA1: disorder(e' e s) < disorder(e e' s)  if e' < e .
open SORTING-STRG-PROOF .
  ops e e' :  -> Elt .
  op s :  -> Strg .
  vars N N' M M' : Nat 
** lemmas about ordering of natural numbers
  eq N < s(N) = true .
--  cq (M + N) < (M + N') = true  if N < N' .
  cq (M + N) + M' < (M + M') + N' = true if (N < N') .
** hypothesis
  eq e' <= e = true .
** conclusion
-- red disorder(e' e s) < disorder(e e' s) .
close

**> LEMMA2: disorder(e s) < disorder(e s')
**> if (e >> s) == (e >> s') and disorder(s) < disorder(s')
open SORTING-STRG-PROOF .
  op e :  -> Elt .
  ops s  s' :  -> Strg .
  vars M M' N : Nat 
** lemma about ordering of natural numbers
  cq (M + N) < (M' + N) = true if (M < M') .
** hypothesis
  eq (e >> s) = (e >> s') .
  eq disorder(s) < disorder(s') = true .
** conclusion
red disorder(e s) < disorder(e s') .
close

-- proof of (generic) local confluence for the sorting algorithm
** case 1 for local confluence 
open SORTING-STRG .
  ops e e' e1 e1' :  -> Elt .
  ops s s' s'' :  -> Strg .
** hypothesis
  eq e'  <= e  = true .
  eq e1' <= e1 = true .
** proof of local confluence
red (s e' e s' e1 e1' s'') ==> (s e' e s' e1' e1 s'') .
red (s e e' s' e1' e1 s'') ==> (s e' e s' e1' e1 s'') .
close
** case 2 for local confluence 
open SORTING-STRG .
  ops e e' e'' :  -> Elt .
  ops s s' :  -> Strg .
** hypothesis
  eq e'  <= e  = true .
  eq e'' <= e' = true .
** lemma
  eq e'' <= e = true .
** proof of local confluence
red (s e' e e'' s') ==> (s e'' e' e s') .
red (s e e'' e' s') ==> (s e'' e' e s') .
close

-- given a fixed string, the following two modules embed
-- the partial order of Z into a total order I-POSET(Z)
-- this embedding is conservative wrt to the execution steps of the
-- sorting algorithm; this is used for proving the generic confluence
-- of the sorting algorithm (see CafeOBJ Jewels for more details)
mod! I-POSET (Y' :: POSET) 
  principal-sort 2Tuple {
  protecting(2TUPLE(Y',NAT))

  op _<=_ : 2Tuple 2Tuple -> Bool

  vars E1 E2 : Elt
  vars N1 N2 : Nat 
    
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true if E1 <= E2 .
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true
     if (E1 <= E2 =/= true) and (E2 <= E1 =/= true) and (N1 <= N2) .
}

mod! STRG-MAPPING (Z :: POSET) {
  protecting(STRG(X <= I-POSET(Y' <= Z))* { sort Strg -> 2Strg } +
	     STRG(X <= Z))

  var E : Elt
  var N : Nat
  var S : Strg
  vars S1 S2 : 2Strg 
 
  op s : 2Tuple -> 2Tuple
  op s : 2Strg -> 2Strg 
    
  op [_] : Elt -> 2Tuple
  op [_] : Strg -> 2Strg 
    
  eq s(<< E ; N >>) = << E ; s(N) >> .
  eq s(S1 S2) =  s(S1) s(S2) .
  
  eq [ E ] = << E ; 1 >> .
  eq [ E S ] = << E ; 1 >> s([ S ]) .
}

open STRG-MAPPING .
  ops e1 e2 e3 e4 e5 :  -> Elt .
red [ e1 e2 e3 e4 e5 ] .
close
--
eof
--
$Id: sorting.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
