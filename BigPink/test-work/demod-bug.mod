-- Return-Path: amori@jaist.ac.jp 
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id PAA26017 for <sawada@sras75.sra.co.jp>; Tue, 14 Dec 1999 15:29:04 +0900
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id PAA21994
-- 	for <sawada@srasva.sra.co.jp>; Tue, 14 Dec 1999 15:28:49 +0859 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id PAA22182
-- 	for <sawada@sra.co.jp>; Tue, 14 Dec 1999 15:29:15 +0900 (JST)
-- Received: from mail.jaist.ac.jp (mex.jaist.ac.jp [150.65.7.20])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id PAA16599
-- 	for <sawada@sra.co.jp>; Tue, 14 Dec 1999 15:29:00 +0900 (JST)
-- Received: from localhost (d194-056 [150.65.194.56]) by mail.jaist.ac.jp (3.7W-jaist_mail) with ESMTP id PAA09846 for <sawada@sra.co.jp>; Tue, 14 Dec 1999 15:28:59 +0900 (JST)
-- To: sawada@sra.co.jp
-- Subject: PigNose bug?
-- Message-Id: <19991214153307O.amori@jaist.ac.jp>
-- Date: Tue, 14 Dec 1999 15:33:07 +0900
-- From: Akira Mori <amori@jaist.ac.jp>
-- X-Dispatcher: imput version 980905(IM100)
-- Mime-Version: 1.0
-- Lines: 233
-- Content-Type: Text/plain; charset=iso-2022-jp
-- Content-Length: 7341

-- 澤田さん，たびたびすいません．さっきとは別件でバグみたいです．

-- 添付のファイル(Lamport アルゴリズム)を食わせると一瞬で反駁してしまいま
-- す．ログも最後につけておきます．

-- ちょっと見てもらえますか．お願いします．

-- 別のやり方ですが，２プロセスの Lamport アルゴリズムの相互排除は完全自
-- 動証明できたと思います．Demodulator がうまく機能してないみたいなので，
-- 手動で公理を加えて処理していますが，早い方の DynaBook で１分ちょっとで
-- す．かなり画期的な結果だと思いますよ．Nプロセスでも大差なくできると思
-- いますが，この辺の scalability が振舞モデル検査の最大の強みでしょうね．

-- では．

-- 森 彰

-- -----------------------------------------------------------------------------
-- the natural numbers
mod! NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  ops 0 : -> NatNum {constr}
  op s : NatNum -> NatNum {constr}
  op _<=_ : NatNum NatNum -> Bool
  op _<_ : NatNum NatNum -> Bool
  vars M N : NatNum
--  ax ~(M < 0) .
  ax ~(M < M) .
  ax M <= M .
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
--  ax ~(s(M) = 0) .
--  ax ~(M < s(0)) | M = 0 .
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
  --
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
  op cust1 :  Shop -> Customer1 { coherent }
  op cust2 :  Shop -> Customer2 { coherent }
  bop Run1 : Shop -> Shop
  bop Run2 : Shop -> Shop
  bop Stat1 : Shop -> Status
  bop Stat2 : Shop -> Status
  bop Ticket1 : Shop -> NatNum
  bop Ticket2 : Shop -> NatNum
  op Init : -> Shop
  var C1 : Customer1   var C2 : Customer2   var S : Shop
  eq cust1(Init) = init1 .
  eq cust2(Init) = init2 .
  beq cust1(Run1(S)) = run1(cust1(S),ticket2(cust2(S))) .
  beq cust2(Run1(S)) = cust2(S) .
  beq cust1(Run2(S)) = cust1(S) .
  beq cust2(Run2(S)) = run2(cust2(S),ticket1(cust1(S))) .
  eq Stat1(S) = stat1(cust1(S)) .
  eq Stat2(S) = stat2(cust2(S)) .
  eq Ticket1(S) = ticket1(cust1(S)) .
  eq Ticket2(S) = ticket2(cust2(S)) .
  eq Ticket1(Run1(Init)) = s(0) .
}

open SHOP .

protecting(FOPL-CLAUSE)

db reset
option reset
-- flag(quiet,on)
-- flag (no-demod,on)
flag(auto,on)
flag(print-stats,on)
flag(universal-symmetry,on)
-- param(max-weight,11)
-- flag(debug-hyper-res,on)
param(max-proofs,1)

var S : Shop .

pred P : Shop .
#define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .

goal \A[S:Shop] P(S) -> P(Run2(S)) .

-- flag(debug-infer,on)
-- flag(debug-hyper-res,on)
-- flag(very-verbose,on)
-- flag(trace-demod,on)
-- flag(print-new-demod,on)

-- resolve /tmp/lamport2+.log

-- 
eof

close

-----------------------------------------------------------------------------
CafeOBJ> in test2
processing input : ./test2.mod
-- defining module! NATNUM
[Warning]: redefining module NATNUM ......._.....* done.
-- defining module! STATUS
[Warning]: redefining module STATUS ......._.......* done.
-- defining module* CUSTOMER1
[Warning]: redefining module CUSTOMER1 ._*........_...........*
** system failed to prove =*= is a congruence of CUSTOMER1 done.
-- defining module* CUSTOMER2
[Warning]: redefining module CUSTOMER2 _*........_...........*
** system failed to prove =*= is a congruence of CUSTOMER2 done.
-- defining module* SHOP
[Warning]: redefining module SHOP _*.............._..........*
** system failed to prove =*= is a congruence of SHOP done.
-- opening module SHOP.. done.
-- setting flag "quiet" to "on"
   dependent: flag(print-message, off)__*_*
 
** PROOF ________________________________
 
  5:[] cust1(Run2(_v1042:Shop)) = cust1(_v1042)
  7:[flip] stat1(cust1(_v1046:Shop)) = Stat1(_v1046)
  11:[] ~(Stat1(#c:Shop-1) = CS) | ~(Stat2(#c:Shop-1) = CS)
  12:[] Stat1(#c:Shop-1) = CS
  28:[] ~(non-CS = CS)
  30:[] ~(please = CS)
  31:[] ~(wait = CS)
  32:[] _v1054:Status = non-CS | _v1054:Status = please | _v1054:Status 
                                                          = 
                                                          wait | 
        _v1054:Status = CS
  132:[para-into:7,5,demod:7,flip] 
    Stat1(Run2(_v1101:Shop)) = Stat1(_v1101)
  134:[back-demod:132,12] Stat1(#c:Shop-1) = CS
  232:[hyper:32,11,32,demod:134,unit-del:31,30,28,28,30,31] 
    
 
** ______________________________________
 
** PigNose statistics ------------------+
|  clauses given            ........26  |
|  clauses generated        .......125  |
|    hyper-res generated    ........45  |
|    para-from generated    ........65  |
|    para-into generated    ........15  |
|    factors generated      .........0  |
|  demod rewrites           ........93  |
|  clauses wt,lit.sk delete ........49  |
|  tautologies deleted      .........0  |
|  clauses forward subsumed ........53  |
|    (subsumed by sos)      .........1  |
|  unit deletions           ........55  |
|  factor simplifications   .......179  |
|  clauses kept             ........76  |
|  new demodulators         ........33  |
|  empty clauses            .........1  |
|  clauses back demodulated .........3  |
|  clauses back subsumed    .........0  |
|  usable size              ........54  |
|  sos size                 ........25  |
|  demodulators size        ........30  |
+---------------------------------------+
CafeOBJ> 

$Id:
