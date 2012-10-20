-- Return-Path: amori@jaist.ac.jp
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.8.8+2.7Wbeta7/3.4W-sra) with ESMTP id WAA23413 for <sawada@sras75.sra.co.jp>; Tue, 18 Jan 2000 22:20:23 +0900 (JST)
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id WAA16999
-- 	for <sawada@srasva.sra.co.jp>; Tue, 18 Jan 2000 22:20:20 +0900 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id WAA21892
-- 	for <sawada@sra.co.jp>; Tue, 18 Jan 2000 22:20:19 +0900 (JST)
-- Received: from mail.jaist.ac.jp (mex.jaist.ac.jp [150.65.7.20])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id WAA06559
-- 	for <sawada@sra.co.jp>; Tue, 18 Jan 2000 22:20:33 +0900 (JST)
-- Received: from localhost (localhost [127.0.0.1]) by mail.jaist.ac.jp (3.7W-jaist_mail) with ESMTP id WAA18459 for <sawada@sra.co.jp>; Tue, 18 Jan 2000 22:20:29 +0900 (JST)
-- To: sawada@sra.co.jp
-- Subject: PigNose?
-- Message-Id: <20000118222725A.amori@jaist.ac.jp>
-- Date: Tue, 18 Jan 2000 22:27:25 +0900
-- From: Akira Mori <amori@jaist.ac.jp>
-- X-Dispatcher: imput version 980905(IM100)
-- Mime-Version: 1.0
-- Content-Type: Text/plain; charset=iso-2022-jp
-- Lines: 162
-- Content-Length: 4778

-- 沢田さん，また素朴な疑問です．

-- 後にあるようなファイルを喰わせると，以下のような節が出て来るのですが，
-- そのあといくら頑張っても 3393 と 429 から ~(stat1(c1) = wait) を導出し
-- てくれないのは何故なんでしょう．max-weight や pick-given-ratio をいろ
-- いろ調節してもダメみたいです．両方とも sos に残っているのになんとなく
-- 不自然な感じがします．よく分かっていないのですが strategy の選択が悪い
-- のでしょうか．neg-hyper-res が要るとか．なわけないですよね．

--   430:[para-into:417,36,unit-del:24] 
--     ~(ticket2(c2) = 0) | ~(stat1(c1) = wait)

--   429:[para-into:417,37,unit-del:24] 
--     ~(ticket1(c1) <= ticket2(c2)) | ~(stat1(c1) = wait)

--   3339:[para-from:2041,419,fsimp:3340] 
--     ticket2(c2) = 0 | ticket1(c1) <= ticket2(c2)

--   3393:[para-from:3339,430,unit-del:42] 
--     ticket1(c1) <= ticket2(c2) | ~(stat1(c1) = wait)

-- 外から見ているだけではよく分からないので，ちょっと教えていただけますか．

-- 森 彰

-- ---------------------------------------------------------------------------
-- the natural numbers
-- mod! NATNUM {
--    protecting(FOPL-CLAUSE)
--    [ NatNum ]
--    ops 0 : -> NatNum
--    op s : NatNum -> NatNum
--    op _<=_ : NatNum NatNum -> Bool
--    op _<_ : NatNum NatNum -> Bool
--    vars M N : NatNum
--    ax ~(s(M) < M) .
--    -- 
--    ax ~(M < M) .
--    --

--    ax 0 < s(0) .
--    ax ~(s(M) <= M) .
--    ax ~(s(M) = 0) .
--    ax 0 <= M .
--    -- ax M = 0 | 0 < M .
-- }

module! NATNUM
{
  protecting (FOPL-CLAUSE)
  protecting (NAT)
  var M : Nat 
  ax M < s M .
  ax ~(s(M) < M) .
  ax ~(M < M) .
  ax ~(s(M) <= M) .
  ax ~(s(M) = 0) .
  ax 0 <= M .
  ax M = 0 | 0 < M .
}

-- the program counters
mod! STATUS {
  protecting(FOPL-CLAUSE)
  [ Status ]
  ops non-CS please wait CS : -> Status
  var S : Status
  ax ~(non-CS = please) .
  ax ~(non-CS = wait) .
  ax ~(non-CS = CS) .
  ax ~(please = wait) .
  ax ~(please = CS) .
  ax ~(wait = CS) .
  ax S = non-CS | S = please | S = wait | S = CS .
}

-- customers
mod* CUSTOMER1 {
  protecting(NATNUM + STATUS)
--  protecting(NAT + STATUS)
  *[ Customer1 ]*
--  op init1 : -> Customer1
  -- attributes
  bop ticket1 : Customer1 -> Nat
  bop stat1 : Customer1 -> Status
  -- methods
  bop run1 : Customer1 Nat -> Customer1
  var C : Customer1  var M : Nat
--  eq stat1(init1) = non-CS .
--  eq ticket1(init1) = 0 .
  ceq stat1(run1(C,M)) = please if stat1(C) == non-CS .
  ceq ticket1(run1(C,M)) = s(0) if stat1(C) == non-CS .
  ceq stat1(run1(C,M))= wait if stat1(C) == please .
  ceq ticket1(run1(C,M)) = s(M) if stat1(C) == please .
  ceq stat1(run1(C,M)) = CS
      if (stat1(C) == wait) and ((M == 0) or (ticket1(C) <= M)) .
  ceq stat1(run1(C,M)) = wait
      if (stat1(C) == wait) and M =/= 0 and (not (ticket1(C) <= M)) .
  ceq ticket1(run1(C,M)) = ticket1(C) if stat1(C) == wait .
  ceq stat1(run1(C,M)) = non-CS if stat1(C) == CS .
  ceq ticket1(run1(C,M)) = 0 if stat1(C) == CS .
}

mod* CUSTOMER2 {
  protecting(NATNUM + STATUS)
  *[ Customer2 ]*
--  op init2 : -> Customer2
  -- attributes
  bop ticket2 : Customer2 -> Nat
  bop stat2 : Customer2 -> Status
  -- methods
  bop run2 : Customer2 Nat -> Customer2
  var C : Customer2  var M : Nat
--  eq stat2(init2) = non-CS .
--  eq ticket2(init2) = 0 .
  ceq stat2(run2(C,M)) = please if stat2(C) == non-CS .
  ceq ticket2(run2(C,M)) = s(0) if stat2(C) == non-CS .
  ceq stat2(run2(C,M))= wait if stat2(C) == please .
  ceq ticket2(run2(C,M)) = s(M) if stat2(C) == please .
  ceq stat2(run2(C,M)) = CS
      if (stat2(C) == wait) and ((M == 0) or (ticket2(C) < M)) .
  ceq stat2(run2(C,M)) = wait
      if (stat2(C) == wait) and M =/= 0 and (not (ticket2(C) < M)) .
  ceq ticket2(run2(C,M)) = ticket2(C) if stat2(C) == wait .
  ceq stat2(run2(C,M)) = non-CS if stat2(C) == CS .
  ceq ticket2(run2(C,M)) = 0 if stat2(C) == CS .
}

-- bakery algorithm
mod* SHOP {
  protecting(CUSTOMER1 + CUSTOMER2)
  *[ Shop ]*
  op shop : Customer1 Customer2 -> Shop { coherent }
--  bop Run : Shop -> Shop
  bop Run1 : Shop -> Shop
  bop Run2 : Shop -> Shop
  bop Stat1 : Shop -> Status
  bop Stat2 : Shop -> Status
  bop Ticket1 : Shop -> Nat
  bop Ticket2 : Shop -> Nat
--  op Init : -> Shop
  var C1 : Customer1   var C2 : Customer2   var S : Shop
--  eq Init = shop(init1,init2) .
--  beq Run(shop(C1,C2)) = shop(run1(C1,ticket2(C2)),run2(C2,ticket1(C1))) .
  beq Run1(shop(C1,C2)) = shop(run1(C1,ticket2(C2)),C2) .
  beq Run2(shop(C1,C2)) = shop(C1,run2(C2,ticket1(C1))) .
  eq Stat1(shop(C1,C2)) = stat1(C1) .
  eq Stat2(shop(C1,C2)) = stat2(C2) .
  eq Ticket1(shop(C1,C2)) = ticket1(C1) .
  eq Ticket2(shop(C1,C2)) = ticket2(C2) .
}

mod* PROOF {

protecting(SHOP)

op c1 : -> Customer1 .
op c2 : -> Customer2 .

pred P : Shop .
#define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .

goal P(Run1(Run1(shop(c1,c2)))) .
}

open PROOF .

db reset
option reset
-- flag(no-demod, on)
flag(auto3, on)
-- flag(order-hyper,off)
-- flag(trace-demod,on)
-- flag(very-verbose,on)
-- flag(binary-res,on)
-- flag(no-new-demod,on)
-- flag(print-kept, on)
-- flag(order-hyper,off)
param(pick-given-ratio, 4)
-- flag(print-stats,on)
flag(universal-symmetry,on)
param(max-weight,22)
param(max-proofs,1)

resolve .

close
**
eof
**
$Id:
