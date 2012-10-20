-- FILE: /home/diacon/LANG/Cafe/prog/hss.mod
-- CONTENTS: behavioural specification of a stack object featuring
--           use of behavioural equations in specifications,
--           definition of behavioural equivalence by parameterized relation
--             and by use of a 2nd order function, and
--           some tests for behavioural context condition in execution
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

-- history sensitive storage (i.e., stack) object
mod* HSS(X :: TRIV) {

  *[ Hss ]*

  bop put : Elt Hss -> Hss
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Elt

  var S : Hss
  var E : Elt

  eq get put(E, S) = E .
  beq rest put(E, S) = S .
}

-- 2nd order rest
mod HSS-PROOF {
  protecting(HSS + BARE-NAT)

  bop rest* : Hss Nat -> Hss 

  vars S S1 S2 : Hss
  vars N N' : Nat
  var E : Elt

  eq  [ p1 ] : rest*(S, s(N)) = rest*(rest S, N) .
  eq  [ p2 ] : rest*(S, 0) = S .
}

-- behavioural equivalence for HSS
mod HSS-BEQ {
  protecting(HSS-PROOF)

  op _R[_]_ : Hss Nat Hss -> Bool

  vars S1 S2 : Hss
  var N : Nat 
        
  eq [ R ] : S1 R[N] S2 = get rest*(S1, N) == get rest*(S2, N) .
}

open HSS-BEQ .
-- proof that _R_ is a hidden congruence 
  ops m n : -> Nat .
  ops e e1 e2 : -> Elt .
  ops s s1 s2 : -> Hss .

  eq [ hyp ] : get rest*(s1, N) = get rest*(s2, N) .
-- -----
--> get |
-- -----
start get s1 == get s2 .
apply -.p2 within term .
apply .hyp within term .
apply reduce at term . -- it should be true
-- ------
--> put |
-- ------
-- proof by case analysis on N 
-- N = 0
red put(e, s1) R[0] put(e, s2) .
-- N = s(n)
red put(e, s1) R[s(n)] put(e, s2) . 
-- -----
--> rest |
-- -----
start (rest s1) R[n] (rest s2) .
apply .R within term .
apply -.p1 within term .
apply .hyp within term .
apply reduce at term .
-- ---------------------------------------------
--> proof of  rest rest put(E1, (put(E2, S))) =b= S .   
-- ---------------------------------------------
red (rest rest put(e1, (put(e2, s)))) R[n] s .

-- ---------------------------------------------
--> proof of  rest*(put(E, S), s(N)) =b= rest*(S, N) .
-- ---------------------------------------------
red (rest*(put(e, s), s(m))) R[n] rest*(s, m) . 
close

-- some tests for the use of behavioural context condition in *reduce*
open HSS(NAT) .
  ops e e1 e2 :  -> Nat .
  ops st st1 st2 :  -> Hss . 
red rest(put(e, st)) == st .
red put(get(rest(put(e1, put(e2, st1)))), st2) == put(e2, st2) .
bred rest(put(e, st)) .
bred rest(put(e, st)) =b= st .
bred rest(put(e, st)) == st .
red rest(put(e, st)) =b= st .
red put(1 + 2, st) == put(3, st) .
close

-- HSS with coherent put method
mod* HSS(X :: TRIV) {

  *[ Hss ]*

  op put : Elt Hss -> Hss   -- coherent
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Elt

  var S : Hss
  var E : Elt

  eq get put(E, S) = E .
  beq rest put(E, S) = S .
}

mod HSS-PROOF {
  protecting(HSS + BARE-NAT)

  bop rest* : Hss Nat -> Hss 

  vars S S1 S2 : Hss
  vars N N' : Nat
  var E : Elt

  eq  [ p1 ] : rest*(S, s(N)) = rest*(rest S, N) .
  eq  [ p2 ] : rest*(S, 0) = S .
}

-- proof for coherence of put
open HSS-PROOF .
  ops s1 s2 :  -> Hss .
  eq get rest*(s1, N) = get rest*(s2, N) .
red get rest*(put(E, s1), 0) == get rest*(put(E, s2), 0) .
red get rest*(put(E, s1), s(N)) == get rest*(put(E, s2), s(N)) .
close

mod* HSS+ { protecting (HSS)
  op put : Elt Hss -> Hss   {coherent}
}	    
	    
--
eof
--
$Id: hss.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
