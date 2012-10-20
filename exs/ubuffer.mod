-- FILE: /home/diacon/LANG/Cafe/prog/ubuffer.mod
-- CONTENTS: behavioural specification of an unreliable buffer object
--           featuring non-determinism and coherent operations
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: *****

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! TRIV+(X :: TRIV) {
  op err :  -> ?Elt 
}

-- reliable buffer object
mod* BUF {
  protecting (TRIV+)

  *[ Buf ]*

  op init :  -> Buf 
  op put : Elt Buf -> Buf   {coherent}
  bop get_ : Buf -> ?Elt
  bop take_ : Buf -> Buf
-- the coherence of empty? cannot be proved as consequence of the spec
-- therefore the BUF-models are restricted only to those for which
-- empty? preserves the behavioural equivalence    
  op empty? : Buf -> Bool   {coherent}

  var E : Elt
  var B : Buf 
        
  eq empty?(init) = true .
  cq empty?(take B) = true if empty?(B) .
  eq empty?(put(E, B)) = false .

  bceq take put(E, B) = put(E, take B) if not empty?(B) .
  bceq take(put(E, B)) = B             if empty?(B) .

  ceq get B = err if empty?(B) .
  cq get put(E, B) = E if empty?(B) .
  cq get put(E, B) = get B if not empty?(B) .
}

open BUF .
  ops e1 e2 : -> Elt .
red get put(e1, put(e2, init)) .
red get take put(e1, init) .
red empty?(take take (put(e1, init))) .
close

--> unreliable buffer object
mod* UBUF {
  protecting (BUF)

  *[ Buf < UBuf ]*

  op put  : Elt  UBuf -> UBuf  {coherent}
  bop take_ : UBuf -> UBuf
    
  op _|_  : UBuf UBuf -> UBuf  {coherent}
  op put? : Elt  UBuf -> UBuf  {coherent}
  op  get? :  Buf ?Elt -> Bool  {coherent}
  bop get? : UBuf ?Elt -> Bool 

  var B : Buf
  vars U1 U2 U : UBuf
  var E  :  Elt
  var E' : ?Elt
        
  eq put (E, U1 | U2)  =  put(E, U1) |  put(E, U2) .
  eq put?(E, U1 | U2)  = put?(E, U1) | put?(E, U2) .
  eq take(   U1 | U2)  = (take   U1) | (take   U2) .
  eq get?(   U1 | U2, E') = get?(U1, E') or get?(U2, E') .  

  eq put?(E, U) = U | put(E, U) .

  eq get?(B, E') = (E' == get B) .
}

open UBUF .
  ops e1 e2 : -> Elt .
  op b : -> Buf .
red           put?(e1, put?(e2, init)) .
red get?(     put?(e1, put?(e2, init)), e1) .
red get?(     put?(e1, put?(e2, init)), e2) .
red get?(     put?(e1, put?(e2, init)), err) .
-- assumption
  eq empty?(b) = false .
red get?(     put?(e1, put?(e2,    b )), err) .
red get?(take put?(e1, put?(e2, init)), e1) .
red get?(take put?(e1, put?(e2, init)), e2) .
red take put(e1, put?(e2, init)) ==  take put?(e1, put(e2, init)) .
red take put(e1, put?(e2, init)) =b= take put?(e1, put(e2, init)) .
close

--> properties valid for reachable UBUF-models
mod* UBUF! {
  protecting(UBUF)

  vars E E' : Elt
  var U : UBuf
    
  eq get?(put(E, U), err) = false .
  cq get?(put(E, U), E') = get?(U, E') 
     if not(get?(U, err)) or (E =/= E' and get?(U, err)) .
  cq get?(put(E, U), E) = true   if get?(U, err) .
  cq get?(take U, err) = true  if get?(U, err) .

  bceq take put(E, U) = put(E, take U)  if not get?(U, err) .
}

-- -----------------------------------------------------
-- BEHAVIOURAL EQUIVALENCES
-- -----------------------------------------------------
mod* BUF-BEQ {
  protecting (BUF + BARE-NAT)

  op _R[_]_ : Buf Nat Buf -> Bool {coherent}

  bop take : Nat Buf -> Buf 

  var N : Nat 
  vars B B1 B2 : Buf 

  eq take(0, B) = B .
  eq take(s(N), B) = take(N, take B) .

  eq B1 R[N] B2 = get take(N, B1) == get take(N, B2) .
}

mod* UBUF-BEQ {
  protecting(UBUF + BUF-BEQ)

  op _R[_,_]_ : UBuf Nat ?Elt UBuf -> Bool {coherent}
  
  bop take : Nat UBuf -> UBuf

  var N : Nat
  var E : ?Elt
  vars U U1 U2 : UBuf

  eq take(0, U) = U .
  eq [take] : take(s(N), U) = take(N, take U) .

  eq  U1 R[N,E] U2 = get?(take(N, U1), E) == get?(take(N, U2), E) .
}

--> environment for proofs
mod* UBUF-PROOF {
  protecting(UBUF-BEQ)
  ops u u' u'' : -> UBuf
  op n  : -> Nat 
  op e  : ->  Elt
  op e' : -> ?Elt

  vars U1 U2 U : UBuf
  var E : Elt 
  var N : Nat 
}

--> take(N, U1 | U2) = take(N, U1) | take(N, U2)
open UBUF-PROOF .
--> base case
red take(0, u | u') == take(0, u) | take(0, u') .
-- induction hypothesis
  eq take(n, U1 | U2) = take(n, U1) | take(n, U2) .
--> induction step
red take(s(n), u | u') == take(s(n), u) | take(s(n), u') .
close

--> proof of behavioural commutativity, associativity, and idempotence of _|_
open UBUF-PROOF .
-- lemma:
  eq take(N, U1 | U2) = take(N, U1) | take(N, U2) .
red (u | u')        R[n,e']  (u' | u) .
red (u | u') | u''  R[n,e']  u | (u' | u'') .
-- Boolean lemmas:
  eq B:Bool and B = B .
  eq B:Bool or  B = B .
red u | u           R[n,e']  u .
close

--> proof of put(e, put?(e, u)) =b= put?(e, put(e, u))
open UBUF-PROOF .
-- lemma:
  eq take(N, U1 | U2) = take(N, U1) | take(N, U2) .
-- conclusion
red put(e, put?(e, u)) R[n,e]  put?(e, put(e, u)) .
red put(e, put?(e, u)) R[n,e'] put?(e, put(e, u)) .
close

--> proof of take put?(e, u) =b= put?(e, take u) if not get?(u, err)
--> for reachable models
open UBUF-PROOF + UBUF! .
-- hypothesis
  eq get?(u, err) = false .
-- conclusion
red take put?(e, u) R[n,e]  put?(e, take u) .
red take put?(e, u) R[n,e'] put?(e, take u) .
close  
--
eof
--
$Id: ubuffer.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
