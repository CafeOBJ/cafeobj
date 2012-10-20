-- FUTATSUGI, Kokichi さんは書きました: 
-- 澤田さん 

-- search commandやerror sortに関連して，ご検討いただいてありがとうございま 
-- す．すでに幾つか未解決の技術的な相談が進行中なのに新しい話で恐縮ですが， 
-- AC matchingに関連した不具合の可能性もあるので，報告しておきます． 

-- search commandを利用して反例発見を行うことは応用上重要と考えていますが， 
-- 緒方さんがAC(assoc-comm)で定義されるbagを使ってNSPK プロトコルの反例発見 
-- を行う例をCafeOBJのsearch commandを使って試みています．これはなかなか面 
-- 白い方法で，緒方さんはすでにこの方法がMaudeで有効に使えることを確かめて 
-- います． 

-- 例題のfileは以下の通りですが，eofの直後のopenの後のsearch commandsの中 
-- で，1番目と2番目は答えが返ってくるのですが，3番目になるとすぐ(10分，20 
-- 分．．．？)では答えが返ってこないようです．4番目，5番目も同様です．2番目 
-- がすぐに答えが返ってくることから，3番目もそれほど時間がかからず，少なく 
-- とも一つ目の答えを帰すと期待されるのですが，そのようには動きません．かな 
-- り大きなACを使ったtermになる可能性はありますが，それだけが原因で時間がか 
-- かるのかが分かりません．何かの事情でAC matchingがうまく動いていない，ま 
-- たは我々が何かCafeOBJのACの動きについて勘違いをしている，という可能性も 
-- 疑われます． 

-- すぐに原因が分かるようであれば教えていただけると幸いです． 

-- 二木 

-- ==================================================================== 

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
  vars R1 R2 : Rand 
  eq (R1 = R1) = true . 
  eq (seed = next(R1)) = false . 
  eq (R1 = next(R1)) = false . 
  eq (next(R1) = next(R2)) = (R1 = R2) . 
} 

mod! NONCE { 
  pr(PRIN + RAND) 
  [Nonce] 
  op n : Prin Prin Rand -> Nonce 
  op p1 : Nonce -> Prin 
  op p2 : Nonce -> Prin 
  op r  : Nonce -> Rand 
  op _=_ : Nonce Nonce -> Bool {comm} 
  vars P1 P2 P12 P22 : Prin 
  vars R1 R2 : Rand 
  var N : Nonce 
  eq p1(n(P1,P2,R1)) = P1 . 
  eq p2(n(P1,P2,R1)) = P2 . 
  eq r(n(P1,P2,R1))  = R1 . 
  eq (N = N) = true . 
  eq (n(P1,P2,R1) = n(P12,P22,R2)) = (P1 = P12 and P2 = P22 and R1 = R2) . 
} 

mod! CIPHER { 
  pr(NONCE) 
  [Cipher] 
  op enc1 : Prin Nonce Prin -> Cipher 
  op enc2 : Prin Nonce Nonce Prin -> Cipher 
  op enc3 : Prin Nonce -> Cipher 
  op k    : Cipher -> Prin 
  op n1   : Cipher -> Nonce 
  op n2   : Cipher -> Nonce 
  op p    : Cipher -> Prin 
  op _=_ : Cipher Cipher -> Bool {comm} 
  vars K1 K2 : Prin 
  vars N1 N2 N11 N21 N12 N22 : Nonce 
  vars P1 P2 : Prin 
  var C : Cipher 
  eq k(enc1(K1,N1,P1)) = K1 . 
  eq k(enc2(K1,N1,N2,P1)) = K1 . 
  eq k(enc3(K1,N1)) = K1 . 
  eq n1(enc1(K1,N1,P1)) = N1 . 
  eq n1(enc2(K1,N1,N2,P1)) = N1 . 
  eq n1(enc3(K1,N1)) = N1 . 
  eq n2(enc2(K1,N1,N2,P1)) = N2 . 
  eq p(enc1(K1,N1,P1)) = P1 . 
  eq p(enc2(K1,N1,N2,P1)) = P1 . 
  eq (C = C) = true . 
  eq (enc1(K1,N11,P1) = enc1(K2,N12,P2)) = (K1 = K2 and N11 = N12 and P1 
= P2) . 
  eq (enc1(K1,N11,P1) = enc2(K2,N12,N22,P2)) = false . 
  eq (enc1(K1,N11,P1) = enc3(K2,N12)) = false . 
  eq (enc2(K1,N11,N21,P1) = enc2(K2,N12,N22,P2)) = 
                     (K1 = K2 and N11 = N12 and N21 = N22 and P1 = P2) . 
  eq (enc2(K1,N11,N21,P1) = enc3(K2,N12)) = false . 
  eq (enc3(K1,N11) = enc3(K2,N12)) = (K1 = K2 and N11 = N12) . 
} 

mod* EQTRIV { 
  pr(TRIV) 
  op _=_ : Elt Elt -> Bool {comm} 
} 

mod! SET (M :: EQTRIV) { 
  [Elt.M < Set] 
  op empty : -> Set 
  op (_ _) : Set Set -> Set {assoc comm} 
  op _\in_ : Elt.M Set -> Bool 
  op _=_ : Set Set -> Bool {comm} 
  vars X X' : Elt.M 
  vars S S' : Set 
  eq (S S) = S . 
  eq X \in empty = false . 
  eq X \in X' = (X = X') . 
  eq X \in (X' S) = (X = X') or (X \in S) . 
  eq (S = S) = true . 
  eq (empty = X S) = false . 
  eq (X = X' S) = false . 
  eq  ((X S) = (X' S')) = (X = X') and (S = S') . 
} 

mod! NONCE-SET { 
  pr((SET(NONCE{sort Elt -> Nonce}))*{sort Set -> NonceSet}) 
} 

-- CIPHER-SET 
mod! NETWORK { 
  pr((SET(CIPHER{sort Elt -> Cipher}))*{sort Set -> Network}) 
} 

mod* NSLPK { 
  pr(NONCE-SET + NETWORK) 
  *[Sys]* 
  -- an arbitrary initial state 
  op init : -> Sys 
  -- observers 
  bop rand   : Sys -> Rand 
  bop nw     : Sys -> Network 
  bop nonces : Sys -> NonceSet 
  -- actions 
  bop send1 : Sys Prin Prin -> Sys 
  bop send2 : Sys Prin Prin Nonce -> Sys 
  bop send3 : Sys Prin Prin Nonce Nonce -> Sys 
  bop fake1 : Sys Prin Prin Nonce -> Sys 
  bop fake2 : Sys Prin Prin Nonce Nonce -> Sys 
  bop fake3 : Sys Prin Nonce -> Sys 
  -- CafeOBJ variables 
  var S : Sys . 
  vars P1 P2 P3 : Prin 
  vars N1 N2 : Nonce 
  -- init 
  eq rand(init)   = seed . 
  eq nw(init)     = empty . 
  eq nonces(init) = empty . 
  -- send1 
  eq rand(send1(S,P1,P2))   = next(rand(S)) . 
  eq nw(send1(S,P1,P2))     = (enc1(P2,n(P1,P2,rand(S)),P1) nw(S)) . 
  eq nonces(send1(S,P1,P2)) = 
      (if P2 = intr then (n(P1,P2,rand(S)) nonces(S)) else nonces(S) fi) . 
  -- send2 
  op c-send2 : Sys Prin Prin Nonce -> Bool 
  eq c-send2(S,P1,P2,N1) = enc1(P1,N1,P2) \in nw(S) . 
  -- 
  ceq rand(send2(S,P1,P2,N1))   = next(rand(S)) if c-send2(S,P1,P2,N1) . 
  ceq nw(send2(S,P1,P2,N1))     = (enc2(P2,N1,n(P1,P2,rand(S)),P1) nw(S)) 
                                  if c-send2(S,P1,P2,N1) . 
  ceq nonces(send2(S,P1,P2,N1)) = 
      (if P2 = intr then (N1 n(P1,P2,rand(S)) nonces(S)) else nonces(S) fi) 
      if c-send2(S,P1,P2,N1) . 
  ceq send2(S,P1,P2,N1)         = S if not c-send2(S,P1,P2,N1) . 
  -- send3 
  op c-send3 : Sys Prin Prin Nonce Nonce -> Bool 
  eq c-send3(S,P1,P2,N1,N2) = enc2(P1,N1,N2,P2) \in nw(S) and 
                              enc1(P2,N1,P1) \in nw(S) . 
  -- 
  eq  rand(send3(S,P1,P2,N1,N2))   = rand(S) . 
  ceq nw(send3(S,P1,P2,N1,N2))     = (enc3(P2,N2) nw(S)) if 
c-send3(S,P1,P2,N1,N2) . 
  ceq nonces(send3(S,P1,P2,N1,N2)) = 
      (if P2 = intr then (N2 nonces(S)) else nonces(S) fi) 
      if c-send3(S,P1,P2,N1,N2) . 
  ceq send3(S,P1,P2,N1,N2)         = S if not c-send3(S,P1,P2,N1,N2) . 
  -- fake1 
  op c-fake1 : Sys Prin Prin Nonce -> Bool 
  eq c-fake1(S,P1,P2,N1) = N1 \in nonces(S) . 
  -- 
  eq  rand(fake1(S,P1,P2,N1))   = rand(S) . 
  ceq nw(fake1(S,P1,P2,N1))     = (enc1(P2,N1,P1) nw(S)) if 
c-fake1(S,P1,P2,N1) . 
  eq  nonces(fake1(S,P1,P2,N1)) = nonces(S) . 
  ceq fake1(S,P1,P2,N1)         = S if not c-fake1(S,P1,P2,N1) . 
  -- fake2 
  op c-fake2 : Sys Prin Prin Nonce Nonce -> Bool 
  eq c-fake2(S,P1,P2,N1,N2) = N1 \in nonces(S) and N2 \in nonces(S) . 
  -- 
  eq  rand(fake2(S,P1,P2,N1,N2))   = rand(S) . 
  ceq nw(fake2(S,P1,P2,N1,N2))     = (enc2(P1,N1,N2,P2) nw(S)) 
                                     if c-fake2(S,P1,P2,N1,N2) . 
  eq  nonces(fake2(S,P1,P2,N1,N2)) = nonces(S) . 
  ceq fake2(S,P1,P2,N1,N2)         = S if not c-fake2(S,P1,P2,N1,N2) . 
  -- fake3 
  op c-fake3 : Sys Prin Nonce -> Bool 
  eq c-fake3(S,P1,N1) = N1 \in nonces(S) . 
  -- 
  eq  rand(fake3(S,P1,N1))   = rand(S) . 
  ceq nw(fake3(S,P1,N1))     = (enc3(P1,N1) nw(S)) if c-fake3(S,P1,N1) . 
  eq  nonces(fake3(S,P1,N1)) = nonces(S) . 
  ceq fake3(S,P1,N1)         = S if not c-fake3(S,P1,N1) . 
} 

eof 

open NSLPK
-- 1 returns an answer 
  red init =(1,1)=>* S . 

-- 2 returns an answer 
  red init =(1,1)=>* ((nonces: Ns) S) . 

-- 3 never return any answer 
  red init =(1,1)=>* ((nonces: (N Ns)) S) . 

-- 4 never return any answer 
  red init =(1,1)=>* ((nonces: (N Ns)) S) suchThat (not(p1(N) == intr or 
p2(N) == intr)) . 

-- 5 never return any answer 
  red init =(1,5)=>* ((nonces: (N Ns)) S) suchThat (not(p1(N) == intr or 
p2(N) == intr)) . 
close 

-- ==================================================================== 
