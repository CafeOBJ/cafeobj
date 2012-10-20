-- Return-Path: amori@jaist.ac.jp 
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id PAA27353 for <sawada@sras75.sra.co.jp>; Wed, 15 Dec 1999 15:20:50 +0900
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id PAA03145
-- 	for <sawada@sras75.sra.co.jp>; Wed, 15 Dec 1999 15:21:05 +0900 (JST)
-- Received: from mail.jaist.ac.jp (mex.jaist.ac.jp [150.65.7.20])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id PAA25088
-- 	for <sawada@sras75.sra.co.jp>; Wed, 15 Dec 1999 15:20:51 +0900 (JST)
-- Received: from localhost (jaist-gate18 [150.65.30.48]) by mail.jaist.ac.jp (3.7W-jaist_mail) with ESMTP id PAA14279 for <sawada@sras75.sra.co.jp>; Wed, 15 Dec 1999 15:20:47 +0900 (JST)
-- To: Toshimi & <sawada@sras75.sra.co.jp>
-- Subject: Re: bug? 
-- In-reply-to: Your message of "Wed, 15 Dec 1999 14:11:39 +0900."
--              <199912150511.OAA27232@sras75.sra.co.jp> 
-- Message-Id: <19991215152501Z.amori@jaist.ac.jp>
-- Date: Wed, 15 Dec 1999 15:25:01 +0900
-- From: Akira Mori <amori@jaist.ac.jp>
-- X-Dispatcher: imput version 980905(IM100)
-- Mime-Version: 1.0
-- Lines: 221
-- Content-Type: Text/plain; charset=iso-2022-jp
-- Content-Length: 6485

-- 澤田さん，ありがとうございます．今日は寒いので在宅勤務しています．

-- まだちょっと具合悪いみたいです．添付のファイルを実行すると


--   26:[] _v277466:Status = non-CS | _v277466:Status = please | 
--         _v277466:Status = wait | _v277466:Status = CS

--   26402:[para-into:26191,41,unit-del:43] 
--     ~(stat1(_v363756:Customer1) = CS) | ~(stat1(run1(run1(_v363756:Customer1,
--                                                           _v363754:NatNum),
--                                                      _v363755:NatNum)) 
--                                           = CS)

--   34587:[hyper:26402,26,26,fsimp:34588,fsimp:34589,fsimp:34590] 
--     stat1(_v392078:Customer1) = non-CS | stat1(_v392078:Customer1) 
--                                          = please | stat1(_v392078:Customer1) 
--                                                     = wait

-- みたいになります．26402 は正しいのですが，34587 を paramodulation で
-- 導出する際に，前と同様に 26402 のもう一方のリテラル

-- ~(stat1(run1(run1(_v363756:Customer1,_v363754:NatNum),_v363755:NatNum)) = CS)

-- が消えてしまっています．

-- すいませんがちょっと見てやって下さい．

-- 森 彰

-- --------------------------------------------------------------------------
-- the natural numbers
mod! NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  ops 0 : -> NatNum
  op s : NatNum -> NatNum
  op _<=_ : NatNum NatNum -> Bool
  op _<_ : NatNum NatNum -> Bool
  vars M N : NatNum
--  ax ~(M < 0) .
--  ax ~(M < M) .
  ax M < s(M) .
--  ax ~(s(M) < M) .
  ax M <= s(M) .
--  ax ~(s(M) <= M) .
--  ax 0 < s(M) .
--  ax ~(M < N) | s(M) < s(N) .
--  ax M < N | ~(s(M) < s(N)) .
--  ax ~(M <= N) | M < N | M = N .
--  ax M <= N | ~(M < N) .
--  ax M <= N | ~(M = N) .
--  ax ~(M = s(M)) .
--  ax 0 <= M .
--  ax M <= N | N < M .
  ax ~(M <= N) | ~(N < M) .
  ax ~(s(M) = 0) .
--  ax ~(M < s(0)) | M = 0 .
--  ax ~(M < s(0)) | M = 0 | M = 1 .
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
  protecting(FOPL-CLAUSE)
  protecting(NATNUM + STATUS)
  *[ Customer1 ]*
  op init1 : -> Customer1
  -- attributes
  bop ticket1 : Customer1 -> NatNum
  bop stat1 : Customer1 -> Status
  -- methods
  bop run1 : Customer1 NatNum -> Customer1
  var C : Customer1  var M : NatNum
  eq stat1(init1) = non-CS .
  eq ticket1(init1) = 0 .
  ceq stat1(run1(C,M)) = please if stat1(C) == non-CS .
  ceq ticket1(run1(C,M)) = s(0) if stat1(C) == non-CS .
  ceq stat1(run1(C,M))= wait if stat1(C) == please .
  ceq ticket1(run1(C,M)) = s(M) if stat1(C) == please .
  ceq stat1(run1(C,M)) = CS
      if (stat1(C) == wait) and ((M == 0) or (ticket1(C) <= M)) .
  ceq stat1(run1(C,M)) = wait
      if (stat1(C) == wait) and not ((M == 0) or (ticket1(C) <= M)) .
  ceq ticket1(run1(C,M)) = ticket1(C) if stat1(C) == wait .
  ceq stat1(run1(C,M)) = non-CS if stat1(C) == CS .
  ceq ticket1(run1(C,M)) = 0 if stat1(C) == CS .
}

mod* CUSTOMER2 {
  protecting(NATNUM + STATUS)
  *[ Customer2 ]*
  op init2 : -> Customer2
  -- attributes
  bop ticket2 : Customer2 -> NatNum
  bop stat2 : Customer2 -> Status
  -- methods
  bop run2 : Customer2 NatNum -> Customer2
  var C : Customer2  var M : NatNum
  eq stat2(init2) = non-CS .
  eq ticket2(init2) = 0 .
  ceq stat2(run2(C,M)) = please if stat2(C) == non-CS .
  ceq ticket2(run2(C,M)) = s(0) if stat2(C) == non-CS .
  ceq stat2(run2(C,M))= wait if stat2(C) == please .
  ceq ticket2(run2(C,M)) = s(M) if stat2(C) == please .
  ceq stat2(run2(C,M)) = CS
      if (stat2(C) == wait) and ((M == 0) or (ticket2(C) < M)) .
  bceq stat2(run2(C,M)) = wait
      if (stat2(C) == wait) and not ((M == 0) or (ticket2(C) < M)) .
  ceq ticket2(run2(C,M)) = ticket2(C) if stat2(C) == wait .
  ceq stat2(run2(C,M)) = non-CS if stat2(C) == CS .
  ceq ticket2(run2(C,M)) = 0 if stat2(C) == CS .
}

-- bakery algorithm
mod* SHOP {
  protecting(CUSTOMER1 + CUSTOMER2)
  *[ Shop ]*
  op shop : Customer1 Customer2 -> Shop { coherent }
--  op cust1 :  Shop -> Customer1 { coherent }
--  op cust2 :  Shop -> Customer2 { coherent }
  bop Run1 : Shop -> Shop
  bop Run2 : Shop -> Shop
  bop Stat1 : Shop -> Status
  bop Stat2 : Shop -> Status
  bop tTicket1 : Shop -> NatNum
  bop tTicket2 : Shop -> NatNum
  op Init : -> Shop
  var C1 : Customer1   var C2 : Customer2   var S : Shop
  eq Init = shop(init1,init2) .
--  eq shop(cust1(S),cust2(S)) = S .
--  eq cust1(shop(C1,C2)) = C1 .
--  eq cust2(shop(C1,C2)) = C2 .
  beq Run1(shop(C1,C2)) = shop(run1(C1,ticket2(C2)),C2) .
  beq Run2(shop(C1,C2)) = shop(C1,run2(C2,ticket1(C1))) .
  eq Stat1(shop(C1,C2)) = stat1(C1) .
  eq Stat2(shop(C1,C2)) = stat2(C2) .
  eq tTicket1(shop(C1,C2)) = ticket1(C1) .
  eq tTicket2(shop(C1,C2)) = ticket2(C2) .
--  eq Ticket1(Run2(S)) = Ticket1(S) .
--  eq Ticket2(Run1(S)) = Ticket2(S) .
--  eq Stat1(Run2(S)) = Stat1(S) .
--  eq Stat2(Run1(S)) = Stat2(S) .
}

open SHOP .

protecting(FOPL-CLAUSE)

db reset
option reset
-- flag(quiet,on)
-- flag(no-demod,on)
-- flag(no-demod,on)
flag(auto,on)
flag(print-stats,on)
flag(universal-symmetry,on)
-- flag(control-memory,off)
-- param(max-weight,18)
param(max-proofs,1)

var S : Shop .

pred P0 : Shop .
pred P1 : Shop .
pred P2 : Shop .
pred P3 : Shop .
pred P : Shop .

#define P0(S:Shop) ::= tTicket1(S) = 0 -> Stat1(S) = non-CS .
-- ok

#define P1(S:Shop) ::= tTicket2(S) = 0 -> Stat2(S) = non-CS .
-- ok

#define P2(S:Shop) ::= (Stat1(S) = CS) -> (Stat2(S) = please | tTicket2(S) = 0 | tTicket1(S) <= tTicket2(S)) .
-- ok

#define P3(S:Shop) ::= (Stat2(S) = CS) -> (Stat1(S) = please | tTicket1(S) = 0 | tTicket2(S) < tTicket1(S)) .
-- ok

#define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .

-- goal P2(Init) .
-- goal \A[C1:Customer1]\A[C2:Customer2] P2(shop(C1,C2)) -> P2(Run1(shop(C1,C2))) .
goal \A[C1:Customer1]\A[C2:Customer2] P(shop(C1,C2)) -> P(Run1(shop(C1,C2))) .


-- ax \A[C1:Customer1]\A[C2:Customer2] P0(shop(C1,C2)) .
-- ax \A[C1:Customer1]\A[C2:Customer2] P1(shop(C1,C2)) .
-- ax \A[C1:Customer1]\A[C2:Customer2] P2(shop(C1,C2)) .
-- ax \A[C1:Customer1]\A[C2:Customer2] P3(shop(C1,C2)) .
-- goal \A[C1:Customer1]\A[C2:Customer2] P(shop(C1,C2)) . 

resolve .

eof
close

-- red Stat1 Run1 Run2 Run2 Run1 Run1 Run2 Run1 init .
-- red Stat2 Run1 Run2 Run2 Run1 Run1 Run2 Run1 init .

**
eof
**
$Id:
