-- Replied: Thu, 27 Jan 2000 20:13:18 +0900
-- Replied: "Akira Mori <amori@jaist.ac.jp> sawada@sra.co.jp"
-- Return-Path: amori@jaist.ac.jp
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.8.8+2.7Wbeta7/3.4W-sra) with ESMTP id PAA04120 for <sawada@sras75.sra.co.jp>; Thu, 27 Jan 2000 15:38:54 +0900 (JST)
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id PAA13339
-- 	for <sawada@srasva.sra.co.jp>; Thu, 27 Jan 2000 15:38:54 +0859 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id PAA02911
-- 	for <sawada@sra.co.jp>; Thu, 27 Jan 2000 15:38:53 +0859 (JST)
-- Received: from mail.jaist.ac.jp (mex.jaist.ac.jp [150.65.7.20])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id PAA17339
-- 	for <sawada@sra.co.jp>; Thu, 27 Jan 2000 15:39:07 +0900 (JST)
-- Received: from localhost (localhost [127.0.0.1]) by mail.jaist.ac.jp (3.7W-jaist_mail) with ESMTP id PAA19768 for <sawada@sra.co.jp>; Thu, 27 Jan 2000 15:39:06 +0900 (JST)
-- To: Toshimi Sawada <sawada@sra.co.jp>
-- Subject: BAKERY Update
-- Message-Id: <20000127154642C.amori@jaist.ac.jp>
-- Date: Thu, 27 Jan 2000 15:46:42 +0900
-- From: Akira Mori <amori@jaist.ac.jp>
-- X-Dispatcher: imput version 980905(IM100)
-- Mime-Version: 1.0
-- Content-Type: Text/plain; charset=iso-2022-jp
-- Lines: 273
-- Content-Length: 9013

-- 澤田さんこんにちは．こっちはまた雪で，すごく寒いです．

-- 宿の件は今日，二木先生と相談して決めます．中川さんはもうしょうがないみ
-- たいですね．今度は私から直接プロジェクトからはずれてもらうように(やん
-- わり)頼むことにします．

-- で，例の BAKERY の例題の最新状況ですが，最後に残っていたゴールの反駁に
-- はいちおう成功したのですが，neg-hyper-res のみを使うという設定でしかダ
-- メでした．PigNose では(というか Otter でも)，節やリテラルの ordering 
-- を積極的に利用しているので，状況によって袋小路に入り込んでしまうのはしょ
-- うがないですね．

-- とりあえずのファイルを添付しますので，澤田さんの方でもいじってみてもら
-- えますか．ただ，ほとんど考えられることは私もやりましたので，最後に残っ
-- ているゴールをなるべくそのままの設定で証明できるような方向で試してもら
-- えるといいと思います．

-- ??? のコメントのついているのが最後の難関です．こいつを反駁するには，

--   * 述語 P の順番が(今と)逆のものにして，
--   * ax S = non-CS | S = please | S = wait | S = CS の代わりを
--     それぞれ CUSTOMER{1,2}で定義し，
--   * flag(hyper-res,off)，flag(neg-hyper-res,on) とする

-- 必要があります．SOS はできるだけ少なくしないと爆発します．

-- あと，あると便利だと思う機能は，

--   * SOS をソースで直接設定できるようにしたい．
--     (今は list axiom で確認してから指定しているが，これだと変更がある度
--      にやり直すのが大変)
--   * flag(universal-symmetry,on) が auto mode 以外でも効いてほしい．
--     (今は auto mode 以外では ax M = M などと直接書かないといけないよう
--     である)
--   * 各ゴールを証明する度に一からソースを読み込んで，process-input して
--     というようだと手間がかかりすぎる．Lisp の fasl みたい形式が欲しい．
--   * ひょっとしたら ur-res の方が sos + hyper-res より微調整が効くかも
--     知れない．

-- 本格的なものとしては，

--   * 不動点の繰り返し計算の漸化式を while 文のようにスクリプト的に定義
--     できると便利(簡易メタ記述機能？)
--   * 前の段階で得られた結果(SOS)のうち，ゴールに依存しない部分を再利用
--     したい(難しそう？)

-- などがあります．究極的には前にも触れたように，可視データ領域専用の決定
-- 手続きを組み込むのが一番だと思います．そうすれば BAKERY の例でも全て数
-- 秒で終るはずだと思っています．Presburger については，考えてみた結果やっ
-- ぱり PVS 方式しかないようです．有限領域については前に触れた有限集合の
-- 記法が最適だと思います．

-- 澤田さんの意見も聞かせてください．

-- 森 彰
-- -------------------------------------------------------------------------
-- the natural numbers
mod! NATNUM {
  protecting(FOPL-CLAUSE)
  [ NatNum ]
  ops 0 : -> NatNum {constr}
  op s : NatNum -> NatNum {constr}
  --  op _<=_ : NatNum NatNum -> Bool
  pred _<_ : NatNum NatNum -- { meta-demod }
  vars M N : NatNum
  ax ~(s(M) < M) .
  ax [no-conf]: ~(s(M) = M) .
  -- ax [no-conf]: ~(s(M) = 0) .
  ax [ax-41]: M < s(M) .
  ax [ax-42]: 0 < s(M) .
  ax [ax-44]: M = 0 | 0 < M .
  ax ~(0 < M)| ~(M = 0) . 
  ax ~(M = N & M < N) .
  ax ~(M < N & N < M) .
  -- ax M < N | M = N | N < M .
  ax ~(M < 0) .
  -- ax M = M .
}

-- the program counters
mod! STATUS {
  protecting(FOPL-CLAUSE)
  [ Status ]
  ops non-CS please wait CS : -> Status { constr }
  ** system generates no-junk, no-confusion axioms
  -- var S : Status
  -- ax [no-conf]: ~(non-CS = please) .
  -- ax [no-conf]: ~(non-CS = wait) .
  -- ax [no-conf]: ~(non-CS = CS) .
  -- ax [no-conf]: ~(please = wait) .
  -- ax [no-conf]: ~(please = CS) .
  -- ax [no-conf]: ~(wait = CS) .
  ** Status is enumerable by finite constants, thus system
  -- will generates 
  -- ax [no-junk]: S = non-CS | S = please | S = wait | S = CS .
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
      if (stat1(C) == wait) and ((M == 0) or (not (M < ticket1(C)))) .
  ceq stat1(run1(C,M)) = wait
      if (stat1(C) == wait) and M =/= 0 and M < ticket1(C) .
  ceq ticket1(run1(C,M)) = ticket1(C) if stat1(C) == wait .
  ceq stat1(run1(C,M)) = non-CS if stat1(C) == CS .
  ceq ticket1(run1(C,M)) = 0 if stat1(C) == CS .
--  ax stat1(C) = non-CS | stat1(C) = please | stat1(C) = wait | stat1(C) = CS .
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
--  ax stat2(C) = non-CS | stat2(C) = please | stat2(C) = wait | stat2(C) = CS .
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

op c1 : -> Customer1 .
op c2 : -> Customer2 .

pred P : Shop .
#define P(S:Shop) ::= ~(Stat1(S) = CS & Stat2(S) = CS) .
-- #define P(S:Shop) ::= ~(Stat2(S) = CS & Stat1(S) = CS) .

ax P(shop(c1,c2)) .

ax P(Run1(shop(c1,c2))) .
ax P(Run2(shop(c1 ,c2))) .

-- goal P(Run1(Run2(shop(c1,c2)))) . -- subsumed by the next
ax P(Run2(Run1(shop(c1,c2)))) .
ax P(Run1(Run1(shop(c1,c2)))) .
ax P(Run2(Run2(shop(c1,c2)))) .

ax P(Run2(Run1(Run1(shop(c1,c2))))) . -- ng when stat1(c1) = please
ax P(Run2(Run1(Run2(shop(c1,c2))))) . -- ng when stat2(c2) = please
ax P(Run1(Run1(Run1(shop(c1,c2))))) . -- ng when stat1(c1) = non-CS
-- goal P(Run1(Run1(Run2(shop(c1,c2))))) . -- subsumed by the other cases
-- goal P(Run2(Run2(Run1(shop(c1,c2))))) . -- subsumed by the other cased
ax P(Run2(Run2(Run2(shop(c1,c2))))) . -- ng when stat2(c2) = non-CS

ax P(Run2(Run1(Run1(Run1(shop(c1,c2)))))) . -- ng when stat1(c1) = non-CS
-- goal P(Run2(Run1(Run1(Run2(shop(c1,c2)))))) . -- ok with sos (*)
-- goal P(Run2(Run1(Run2(Run1(shop(c1,c2)))))) . -- ok with sos (*)
ax P(Run2(Run1(Run2(Run2(shop(c1,c2)))))) . -- ng when stat2(c2) = non-CS
-- goal P(Run1(Run1(Run1(Run1(shop(c1,c2)))))) . -- ok with sos (*)
-- goal P(Run1(Run1(Run1(Run2(shop(c1,c2)))))) . -- ok with sos (*)
-- goal P(Run2(Run2(Run2(Run1(shop(c1,c2)))))) . -- ok with sos (*)
-- goal P(Run2(Run2(Run2(Run2(shop(c1,c2)))))) . -- ok with sos (*)

-- goal P(Run2(Run1(Run1(Run1(Run1(shop(c1,c2))))))) . -- ok with sos (*)
goal [ax-13]: P(Run2(Run1(Run1(Run1(Run2(shop(c1,c2))))))) . -- ok ok with sos (+)
-- goal P(Run2(Run1(Run2(Run2(Run1(shop(c1,c2))))))) . -- ???
-- goal P(Run2(Run1(Run2(Run2(Run2(shop(c1,c2))))))) . -- ok ok with sos (+)
}

open PROOF .
 
db reset
option reset
-- flag(no-junk,off)
-- flag(no-confusion,off)

flag(process-input, on)
flag(print-kept, off)
flag(print-new-demod, off)
flag(print-back-demod, off)
flag(print-back-sub, off)
flag(control-memory, on)
param(max-sos, 500).
param(pick-given-ratio, 4).
param(stats-level, 1).
param(max-seconds, 3600).
flag(kb2, on)
-- flag(para-from, on)
-- flag(para-into, on)
-- flag(para-from-right, off)
-- flag(para-into-right, off)
-- flag(para-from-vars, off)
-- flag(eq-units-both-ways, on)
-- flag(dynamic-demod-all, on)
-- flag(dynamic-demod, on)
-- flag(order-eq, on)
-- flag(back-demod, on)
-- flag(lrpo, on)
flag(hyper-res, on)
flag(unit-deletion, on)
flag(factor, on)
-- flag(back-sub,off)
-- flag(prop-res, off)
-- flag(neg-hyper-res, on)
-- flag(order-hyper, on)
-- flag(binary-res, on)
-- flag(no-new-demod, on)
-- flag(para-into-vars, on)

flag(print-stats,on)
flag(universal-symmetry,on)
-- param(max-weight,28)
param(max-proofs,1)

-- sos = { 13 14 41 42 44 } -- (+)
sos = { ax-13 ax-41 ax-42 ax-44 } -- (+)

-- sos = { 13 14 42 43 45 }

-- sos = { 13 14 } -- (*)

resolve .

close
--
eof
--
$Id
