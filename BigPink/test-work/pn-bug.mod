-- Return-Path: amori@mb2.em.nttpnet.ne.jp
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.8.8+2.7Wbeta7/3.4W-sra) with ESMTP id MAA20848 for <sawada@sras75.sra.co.jp>; Sun, 16 Jan 2000 12:57:21 +0900 (JST)
-- From: amori@mb2.em.nttpnet.ne.jp
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id MAA11841
-- 	for <sawada@srasva.sra.co.jp>; Sun, 16 Jan 2000 12:57:17 +0900 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id MAA19981
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 12:57:17 +0900 (JST)
-- Received: from IGW00.pmc.nttpnet.ne.jp (igw00.pmc.nttpnet.ne.jp [210.153.107.152])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id MAA00376
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 12:57:31 +0900 (JST)
-- Received: from MGW00.pm0.nttpnet.ne.jp ([100.1.158.100] (may be forged))
-- 	by IGW00.pmc.nttpnet.ne.jp (8.8.6 (PHNE_17135)/8.8.6) with ESMTP id NAA17779
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 13:00:20 +0900 (JST)
-- Received: from SRS00.pm0.nttpnet.ne.jp (SRS00.pm0.nttpnet.ne.jp [100.1.10.100])
-- 	by MGW00.pm0.nttpnet.ne.jp (8.8.6 (PHNE_17135)/8.8.6) with ESMTP id MAA16701
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 12:57:06 +0900 (JST)
-- Received: from nttphs (MROUTE00.pm0.nttpnet.ne.jp [100.1.100.100])
-- 	by SRS00.pm0.nttpnet.ne.jp (8.8.6 (PHNE_17135)/3.7W) with SMTP id MAA23204
-- 	for sawada@sra.co.jp; Sun, 16 Jan 2000 12:55:55 +0900 (JST)
-- Date: Sun, 16 Jan 2000 12:55:55 +0900 (JST)
-- Message-Id: <200001160355.MAA23204@SRS00.pm0.nttpnet.ne.jp>
-- To: sawada@sra.co.jp
-- Subject: Q
-- MIME-Version: 1.0
-- Content-Type: text/plain; charset="iso-2022-jp"
-- Content-Transfer-Encoding: 7bit
-- X-Mailer: Paldio Palmtop Mail (UNKNOWN, unknown)
-- X-PAD-Processed: Sun, 16 Jan 2000 13:04:05 +0900 (JST)
-- Content-Length: 1096


-- 澤田さん，連絡が滞っていてすいません．JAIST 訪問の件は，二木先生が忙し
-- いようなのでちょっと無理みたいです．

-- PigNose を使っていてちょっと気になったことがあります．例の Bakery アル
-- ゴリズム の(変種の)証明を試しているのですが，その中で，

-- #18(weight=4):
--   130:[para-into:127,25,unit-del:29] 
--     ~(stat2(c2) = CS)
-- #19(weight=4):
--   134:[para-into:127,19,unit-del:32] 
--     ~(stat2(c2) = please)
-- #20(weight=4):
--   135:[para-into:127,17,unit-del:31] 
--     ~(stat2(c2) = non-CS)
-- #21(weight=12):
--   33:[] _v644094:Status = non-CS | _v644094:Status = please | 
--         _v644094:Status = wait | _v644094:Status = CS
-- #22(weight=4):
--   152:[hyper:33,135,unit-del:130,134] 
--     wait = wait

-- のようになって，stat2(c2) = wait が(永遠に)導出されません．微妙なバグ
-- のような気がするのですが，ちょっと見ていただけますか．

-- 関係ないですが，先日 CS放送で CC の Hangin' Around のビデオ見ました．
-- かっこうよかったですよ．例の科技庁の公募の相談で，来週あたり出張するか
-- も知れません．

-- 森 彰

-- Return-Path: amori@mb2.em.nttpnet.ne.jp
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.8.8+2.7Wbeta7/3.4W-sra) with ESMTP id NAA20861 for <sawada@sras75.sra.co.jp>; Sun, 16 Jan 2000 13:19:43 +0900 (JST)
-- From: amori@mb2.em.nttpnet.ne.jp
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id NAA11956
-- 	for <sawada@srasva.sra.co.jp>; Sun, 16 Jan 2000 13:19:39 +0900 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id NAA20224
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 13:19:39 +0900 (JST)
-- Received: from IGW00.pmc.nttpnet.ne.jp (igw00.pmc.nttpnet.ne.jp [210.153.107.152])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id NAA00785
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 13:19:50 +0900 (JST)
-- Received: from MGW00.pm0.nttpnet.ne.jp ([100.1.158.100] (may be forged))
-- 	by IGW00.pmc.nttpnet.ne.jp (8.8.6 (PHNE_17135)/8.8.6) with ESMTP id NAA22761
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 13:22:38 +0900 (JST)
-- Received: from SRS00.pm0.nttpnet.ne.jp (SRS00.pm0.nttpnet.ne.jp [100.1.10.100])
-- 	by MGW00.pm0.nttpnet.ne.jp (8.8.6 (PHNE_17135)/8.8.6) with ESMTP id NAA23306
-- 	for <sawada@sra.co.jp>; Sun, 16 Jan 2000 13:19:22 +0900 (JST)
-- Received: from nttphs (MROUTE00.pm0.nttpnet.ne.jp [100.1.100.100])
-- 	by SRS00.pm0.nttpnet.ne.jp (8.8.6 (PHNE_17135)/3.7W) with SMTP id NAA10546
-- 	for sawada@sra.co.jp; Sun, 16 Jan 2000 13:18:09 +0900 (JST)
-- Date: Sun, 16 Jan 2000 13:18:09 +0900 (JST)
-- Message-Id: <200001160418.NAA10546@SRS00.pm0.nttpnet.ne.jp>
-- To: sawada@sra.co.jp
-- Subject: Re: Q
-- MIME-Version: 1.0
-- Content-Type: text/plain; charset="iso-2022-jp"
-- Content-Transfer-Encoding: 7bit
-- X-Mailer: Paldio Palmtop Mail (UNKNOWN, unknown)
-- X-PAD-Processed: Sun, 16 Jan 2000 13:26:19 +0900 (JST)
-- Content-Length: 4138

-- CafeOBJ のソースも送っておきます．よろしくお願いします．

-- the natural numbers
mod! NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  ops 0 : -> NatNum
  op s : NatNum -> NatNum
  op _<=_ : NatNum NatNum -> Bool
  op _<_ : NatNum NatNum -> Bool
  vars M N : NatNum
  ax M < s(M) .
  ax M <= s(M) .
  ax ~(s(M) = 0) .
  ax M <= N | N < M .
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
  *[ Customer1 ]*
--  op init1 : -> Customer1
  -- attributes
  bop ticket1 : Customer1 -> NatNum
  bop stat1 : Customer1 -> Status
  -- methods
  bop run1 : Customer1 NatNum -> Customer1
  var C : Customer1  var M : NatNum
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
  bop ticket2 : Customer2 -> NatNum
  bop stat2 : Customer2 -> Status
  -- methods
  bop run2 : Customer2 NatNum -> Customer2
  var C : Customer2  var M : NatNum
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
  bop Ticket1 : Shop -> NatNum
  bop Ticket2 : Shop -> NatNum
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

var S : Shop .
var C1 : Customer1 .
var C2 : Customer2 .

op c1 : -> Customer1 .
op c2 : -> Customer2 .

pred P : Shop .
#define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .

ax P(shop(c1,c2)) .

ax P(Run1(shop(c1,c2))) .
ax P(Run2(shop(c1,c2))) .

-- goal P(Run1(Run2(shop(c1,c2)))) . -- subsumed by the next
ax P(Run2(Run1(shop(c1,c2)))) .
ax P(Run1(Run1(shop(c1,c2)))) .
ax P(Run2(Run2(shop(c1,c2)))) .

ax P(Run2(Run1(Run2(shop(c1,c2))))) .
ax P(Run1(Run1(Run1(shop(c1,c2))))) .
goal P(Run1(Run1(Run2(shop(c1,c2))))) .
-- ax P(Run2(Run2(Run1(shop(c1,c2))))) .
-- ax P(Run2(Run2(Run2(shop(c1,c2))))) .
}

open PROOF .

db reset
option reset
flag(auto3, on)
param(pick-given-ratio, 4).
flag(print-stats,on)
flag(universal-symmetry,on)
param(max-weight,22)
param(max-proofs,1)
-- flag(print-back-demod,on)
-- flag(print-new-demod,on)
-- flag(print-kept,on)
-- flag(trace-demod,on)
-- flag(debug-infer,on)
-- flag(print-kept,on)
-- flag(very-verbose,on)
-- flag(debug-para-into,on)
resolve .

--
eof

close

**
eof
**
$Id:
