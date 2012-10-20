mod* PRIN {
  [Prin]
  op intr : -> Prin 
}

mod! RAND {
  [Rand]
  op seed : -> Rand 
  op next : Rand -> Rand
}

mod! NONCE {
  pr(PRIN)
  pr(RAND)
  [Nonce]
  op n : Prin Prin Rand -> Nonce
  op p1 : Nonce -> Prin
  op p2 : Nonce -> Prin
  vars P1 P2 : Prin
  var R : Rand
  eq p1(n(P1,P2,R)) = P1 .
  eq p2(n(P1,P2,R)) = P2 .
}

mod! CIPHER {
  pr(NONCE)
  [Cipher]
  op enc1 : Prin Nonce Prin -> Cipher
  op enc2 : Prin Nonce Nonce -> Cipher
  op enc3 : Prin Nonce -> Cipher
}

mod! NONCEBAG {
  pr(NONCE)
  [Nonce < NonceBag]
  op empty : -> NonceBag
  op __ : NonceBag NonceBag -> NonceBag {assoc comm id: empty}
}

mod! NETWORK {
  pr(CIPHER)
  [Cipher < Network]
  op empty : -> Network 
  op __ : Network Network -> Network {assoc comm id: empty}
}

mod NSPK {
  pr(NONCEBAG)
  pr(NETWORK)
  [Transition Observer < Sys]
  -- Configuration
  op none : -> Sys
  op __ : Sys Sys -> Sys {assoc comm id: none}
  -- Observable values 
  op rand:_   : Rand       -> Observer
  op nw:_     : Network    -> Observer
  op nonces:_ : NonceBag   -> Observer
  -- Transition rules
  op send1 : Prin Prin -> Transition
  op send2 : -> Transition
  op send3 : -> Transition
  op fake1 : -> Transition
  op fake2 : -> Transition
  op fake3 : -> Transition
  -- CafeOBJ variables
  var R : Rand
  vars N N1 N2 : Nonce
  vars P1 P2 P3 : Prin
  var NW : Network
  var Ns : NonceBag
  -- Transition rules
  -- send1
  trans [send1] : 
    send1(P1,P2) (rand: R) (nw: NW) (nonces: Ns)
    => send1(P1,P2) (rand: next(R)) (nw: (enc1(P2,n(P1,P2,R),P1) NW)) 
       (nonces: (if P2 == intr then n(P1,P2,R) Ns else Ns fi)) .
  -- send2
  trans [send2] :
    send2 (rand: R) (nw: (enc1(P1,N,P2) NW)) (nonces: Ns)
    => send2 (rand: next(R)) (nw: (enc2(P2,N,n(P1,P2,R)) enc1(P1,N,P2) NW)) 
       (nonces: (if P2 == intr then N n(P1,P2,R) Ns else Ns fi)) .
  -- send3
  trans [send3] :
    send3 (rand: R) (nw: (enc2(P1,N1,N2) enc1(P2,N1,P1) NW)) (nonces: Ns)
    => send3 (rand: R) (nw: (enc3(P2,N2) enc2(P1,N1,N2) enc1(P2,N1,P1) NW)) 
       (nonces: (if P2 == intr then N2 Ns else Ns fi)) .
  -- fake1
  trans [fake1] :
    fake1 (nw: NW) (nonces: (N Ns)) 
    => fake1 (nw: (enc1(P2,N,P1) NW)) (nonces: (N Ns)) . 
  -- fake2
  trans [fake2] :
    fake2 (nw: NW) (nonces: (N1 N2 Ns))
    => fake2 (nw: (enc2(P2,N1,N2) NW)) (nonces: (N1 N2 Ns)) .
  -- fake3
  trans [fake3] :
    fake3 (nw: NW) (nonces: (N Ns))
    => fake3 (nw: (enc3(P2,N) NW)) (nonces: (N Ns)) .
}

mod NSPK-INIT {
  pr(NSPK)
  ops p1 p2 : -> Prin 
  op init : -> Sys
  vars N N1 N2 : Nonce
  vars P1 P2 P3 P4 P5 : Prin
  var Ns : NonceBag
  var NW : Network
  var R : Rand
  var S : Sys
  eq init = send1(p1,p2) send1(p1,intr) send1(p2,p1) send1(p2,intr) send1(intr,p1) send1(intr,p2) 
            send2 send3 fake1 fake2 fake3
            (rand: seed) (nw: empty) (nonces: empty) .
}

eof

open NSPK-INIT
  red init =(1,1)=>* S .

  red init =(1,1)=>* ((nonces: Ns) S) .

  red init =(1,1)=>* ((nonces: (N Ns)) S) .

  red init =(1,1)=>* ((nonces: (N Ns)) S) suchThat (not(p1(N) == intr or p2(N) == intr)) .

  red init =(1,5)=>* ((nonces: (N Ns)) S) suchThat (not(p1(N) == intr or p2(N) == intr)) .
close


