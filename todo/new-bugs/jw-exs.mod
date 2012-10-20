mod! STRG (X :: TRIV) {
  [ Elt < Strg ]

  op nil :  -> Elt 
  op __ : Strg Strg -> Strg {assoc idr: nil} 
}

mod* POSET {
  [ Elt ]

  op _<=_ : Elt Elt -> Bool 

  vars E1 E2 E3 : Elt

  eq E1 <= E1 = true .
  cq E1 = E2      if (E1 <= E2) and (E2 <= E1) .
  cq (E1 <= E3) = true      if (E1 <= E2) and (E2 <= E3) .
}

mod! SORTING-STRG(Y :: POSET) {
  protecting(STRG(Y))
  
  ctrans N:Elt N':Elt => N' N  if (N' <= N) and (N =/= N') .
}

select SORTING-STRG(NAT)
exec (4 3 5 3 1) .

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
red disorder(e' e s) < disorder(e e' s) .
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

** case 1 for local confluence 
open SORTING-STRG .
  ops e e' e1 e1' :  -> Elt .
  ops s s' s'' :  -> Strg .
** hypothesis
  eq e' <= e = true .
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
  eq e' <= e = true .
  eq e'' <= e' = true .
** lemma
  eq e'' <= e = true .
** proof of local confluence
red (s e' e e'' s') ==> (s e'' e' e s') .
red (s e e'' e' s') ==> (s e'' e' e s') .
close

mod! I-POSET (Y' :: POSET) {
  protecting(2TUPLE(Y',NAT))

  op _<=_ : 2Tuple 2Tuple -> Bool

  vars E1 E2 : Elt
  vars N1 N2 : Nat 
    
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true if E1 <= E2 .
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true
     if (E1 <= E2 =/= true) and (E2 <= E1 =/= true) and (N1 <= N2) .
}

mod! STRG-MAPPING (Z :: POSET) {
  protecting(STRG(Z) +
	     STRG(I-POSET(Z){sort Elt -> 2Tuple})* { sort Strg -> 2Strg })

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













