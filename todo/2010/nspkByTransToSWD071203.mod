mod* PRIN {
  [Prin]
  op intr : -> Prin 
  op _=_ : Prin Prin -> Bool {comm}
  var P : Prin 
  eq (P = P) = true .
}

mod! RAND {
  [Rand]
  op seed : -> Rand 
  op next : Rand -> Rand
  op _=_ : Rand Rand -> Bool {comm}
  vars R R1 R2 : Rand 
  eq (R = R) = true .
  eq (seed = next(R)) = false .
  eq (R = next(R)) = false .
  eq (next(R1) = next(R2)) = (R1 = R2) .
}

mod! NONCE {
  pr(PRIN)
  pr(RAND)
  [Nonce]
  op n : Prin Prin Rand -> Nonce
  op p1 : Nonce -> Prin
  op p2 : Nonce -> Prin
  op r  : Nonce -> Rand
  op _=_ : Nonce Nonce -> Bool {comm}
  vars P1 P2 P12 P22 : Prin
  vars R R1 R2 : Rand
  var N : Nonce
  eq p1(n(P1,P2,R)) = P1 .
  eq p2(n(P1,P2,R)) = P2 .
  eq r(n(P1,P2,R))  = R .
  eq (N = N) = true .
  eq (n(P1,P2,R1) = n(P12,P22,R2)) = (P1 = P12 and P2 = P22 and R1 = R2) .
}

mod! CIPHER {
  pr(NONCE)
  [Cipher]
  op enc1 : Prin Nonce Prin -> Cipher
  op enc2 : Prin Nonce Nonce -> Cipher
  op enc3 : Prin Nonce -> Cipher
  op k    : Cipher -> Prin
  op n1   : Cipher -> Nonce
  op n2   : Cipher -> Nonce
  op p    : Cipher -> Prin
  op _=_  : Cipher Cipher -> Bool {comm}
  vars K K1 K2 : Prin
  vars N1 N2 N11 N21 N12 N22 : Nonce
  vars P P1 P2 : Prin
  var C : Cipher
  eq k(enc1(K,N1,P)) = K .
  eq k(enc2(K,N1,N2)) = K .
  eq k(enc3(K,N1)) = K .
  eq n1(enc1(K,N1,P)) = N1 .
  eq n1(enc2(K,N1,N2)) = N1 .
  eq n1(enc3(K,N1)) = N1 .
  eq n2(enc2(K,N1,N2)) = N2 .
  eq p(enc1(K,N1,P)) = P .
  eq (C = C) = true .
  eq (enc1(K1,N11,P1) = enc1(K2,N12,P2)) = (K1 = K2 and N11 = N12 and P1 = P2) .
  eq (enc1(K1,N11,P1) = enc2(K2,N12,N22)) = false .
  eq (enc1(K1,N11,P1) = enc3(K2,N12)) = false .
  eq (enc2(K1,N11,N21) = enc2(K2,N12,N22)) = (K1 = K2 and N11 = N12 and N21 = N22) .
  eq (enc2(K1,N11,N21) = enc3(K2,N12)) = false .
  eq (enc3(K1,N11) = enc3(K2,N12)) = (K1 = K2 and N11 = N12) .
}

mod! MSG {
  pr(CIPHER)
  [Msg]
  -- 1. creator, 2. (seeming) sender, 3. receiver, 4. body
  op m : Prin Prin Prin Cipher -> Msg
  op c : Msg -> Prin
  op s : Msg -> Prin
  op r : Msg -> Prin
  op b : Msg -> Cipher
  op _=_ : Msg Msg -> Bool {comm}
  var M : Msg
  vars C C1 : Prin
  vars S S1 : Prin
  vars R R1 : Prin
  vars B B1 : Cipher
  eq c(m(C,S,R,B)) = C .
  eq s(m(C,S,R,B)) = S .
  eq r(m(C,S,R,B)) = R .
  eq b(m(C,S,R,B)) = B .
  eq (M = M) = true .
  eq (m(C,S,R,B) = m(C1,S1,R1,B1)) 
     = (C = C1 and S = S1 and R = R1 and B = B1) .
}

mod! NONCEBAG {
  pr(NONCE)
  [Nonce < NonceBag]
  op empty : -> NonceBag
  op __ : NonceBag NonceBag -> NonceBag {assoc comm id: empty}
  op _\in_ : Nonce NonceBag -> Bool
  op _=_ : NonceBag NonceBag -> Bool {comm}
  vars N N1 : Nonce
  vars B B1 : NonceBag
  eq N \in empty = false .
  eq N \in (N1 B) = (N = N1 or N \in B) .
  eq (B = B) = true .
  eq (empty = N B) = false .
  eq (N B = N1 B1) = (N = N1 and B = B1) .
}

mod! NETWORK {
  pr(MSG)
  [Msg < Network]
  op empty : -> Network 
  op __ : Network Network -> Network {assoc comm id: empty}
  op _\in_ : Msg Network -> Bool
  op _=_ : Network Network -> Bool {comm}
  vars NW NW1 : Network 
  vars M M1 : Msg
  eq M \in empty = false .
  eq M \in (M1 NW) = (M = M1 or M \in NW) .
  eq (NW = NW) = true .
  eq (empty = M NW) = false .
  eq (M NW = M1 NW1) = (M = M1 and NW = NW1) .
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
  op fake1 : Prin Prin -> Transition
  op fake2 : Prin Prin -> Transition
  op fake3 : Prin Prin -> Transition
  op fake4 : Prin Prin -> Transition
  -- CafeOBJ variables
  var R : Rand
  vars N N1 N2 : Nonce
  vars P1 P2 P3 : Prin
  var M : Msg
  var NW : Network
  var Ns : NonceBag
  -- Transition rules
  -- send1
  trans [send1] : 
    send1(P1,P2) (rand: R) (nw: NW) (nonces: Ns)
    => send1(P1,P2) (rand: next(R)) (nw: (m(P1,P1,P2,enc1(P2,n(P1,P2,R),P1)) NW)) (nonces: (if P2 == intr then n(P1,P2,R) Ns else Ns fi)) .
  -- send2
  trans [send2] :
    send2 (rand: R) (nw: (m(P3,P2,P1,enc1(P1,N,P2)) NW)) (nonces: Ns)
    => send2 (rand: next(R)) (nw: (m(P1,P1,P2,enc2(P2,N,n(P1,P2,R))) m(P3,P2,P1,enc1(P1,N,P2)) NW)) (nonces: (if P2 == intr then N n(P1,P2,R) Ns else Ns fi)) .
  -- send3
  trans [send3] :
    send3 (rand: R) (nw: (m(P3,P2,P1,enc2(P1,N1,N2)) m(P1,P1,P2,enc1(P2,N1,P1)) NW)) (nonces: Ns)
    => send3 (rand: R) (nw: (m(P1,P1,P2,enc3(P2,N2)) m(P3,P2,P1,enc2(P1,N1,N2)) m(P1,P1,P2,enc1(P2,N1,P1)) NW)) (nonces: (if P2 == intr then N2 Ns else Ns fi)) .
  -- fake1
  trans [fake1] :
    fake1(P1,P2) (nw: NW) (nonces: (N Ns)) 
    => fake1(P1,P2) (nw: (m(intr,P1,P2,enc1(P2,N,P1)) NW)) (nonces: (N Ns)) . 
  -- fake2
  trans [fake2] :
    fake2(P1,P2) (nw: NW) (nonces: (N1 N2 Ns))
    => fake2(P1,P2) (nw: (m(intr,P1,P2,enc2(P2,N1,N2)) NW)) (nonces: (N1 N2 Ns)) .
  -- fake3
  trans [fake3] :
    fake3(P1,P2) (nw: NW) (nonces: (N Ns))
    => fake3(P1,P2) (nw: (m(intr,P1,P2,enc3(P2,N)) NW)) (nonces: (N Ns)) .
  -- fake4
  trans [fake4] :
    fake4(P1,P2) (nw: (M NW))
    => fake4(P1,P2) (nw: (m(intr,P1,P2,b(M)) M NW)) .
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
            send2 send3
            fake1(p1,p2) fake1(p1,intr) fake1(p2,p1) fake1(p2,intr) fake1(intr,p1) fake1(intr,p2) 
            fake2(p1,p2) fake2(p1,intr) fake2(p2,p1) fake2(p2,intr) fake2(intr,p1) fake2(intr,p2) 
            fake3(p1,p2) fake3(p1,intr) fake3(p2,p1) fake3(p2,intr) fake3(intr,p1) fake3(intr,p2) 
            fake4(p1,p2) fake4(p1,intr) fake4(p2,p1) fake4(p2,intr) fake4(intr,p1) fake4(intr,p2) 
            (rand: seed) (nw: empty) (nonces: empty) .
}

eof

open NSPK-INIT
-- 1 returns an answer
   red init =(1,1)=>* S .

-- 2 returns an answer
   red init =(1,1)=>* ((nonces: Ns) S) .

-- 3 never return any answer
   red init =(1,1)=>* ((nonces: (N Ns)) S) .

-- 4 never return any answer
   red init =(1,1)=>* ((nonces: (N Ns)) S) 
     suchThat (not(p1(N) == intr or p2(N) == intr)) .

-- 5 never return any answer
   red init =(1,5)=>* ((nonces: (N Ns)) S) 
     suchThat (not(p1(N) == intr or p2(N) == intr)) .
close
