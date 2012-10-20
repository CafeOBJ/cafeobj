-- Return-Path: cafeteria-request@rascal.jaist.ac.jp 
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id PAA13472 for <sawada@sras75.sra.co.jp>; Mon, 21 Apr 1997 15:39:10 +0900
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8]) by srasva.sra.co.jp (8.6.12+2.4W3/3.4W-srambox) with ESMTP id PAA14689 for <sawada@srasva.sra.co.jp>; Mon, 21 Apr 1997 15:41:10 +0900
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14]) by sranha.sra.co.jp (8.6.13/3.4W-sranha) with ESMTP id PAA27637 for <sawada@sra.co.jp>; Mon, 21 Apr 1997 15:40:43 +0900
-- Received: from mikan.jaist.ac.jp by sraigw.sra.co.jp (8.6.13/3.4W-sraigw)
--	id PAA16491; Mon, 21 Apr 1997 15:40:55 +0859
-- Received: from rascal.jaist.ac.jp ( <cafeteria-request@rascal.jaist.ac.jp>) by mikan.jaist.ac.jp (8.7.5); id PAA26616; Mon, 21 Apr 1997 15:41:03 +0900 (JST)
-- Received: (from slist@localhost)
-- 	by rascal.jaist.ac.jp (8.8.5/8.8.5) id PAA14786;
-- 	Mon, 21 Apr 1997 15:39:44 +0900 (JST)
-- Resent-Date: Mon, 21 Apr 1997 15:39:44 +0900 (JST)
-- X-Authentication-Warning: rascal.jaist.ac.jp: slist set sender to cafeteria-request@ldl.jaist.ac.jp using -f
-- From: Michihiro Matumoto <mitihiro@jaist.ac.jp>
-- Date: Mon, 21 Apr 97 15:39:37 JST
-- Message-Id: <9704210639.AA12918@is27e0s04.jaist.ac.jp>
-- To: cafeteria@rascal.jaist.ac.jp
-- Subject: Problem about bop .
-- Resent-Message-ID: <"oSRoWC.A.9mD.wuwWz"@rascal.jaist.ac.jp>
-- Resent-From: cafeteria@rascal.jaist.ac.jp
-- Reply-To: cafeteria@rascal.jaist.ac.jp
-- X-Mailing-List: <cafeteria@ldl.jaist.ac.jp> archive/latest/133
-- X-Loop: cafeteria@ldl.jaist.ac.jp
-- Precedence: list
-- Resent-Sender: cafeteria-request@rascal.jaist.ac.jp
-- Content-Type: text
-- Content-Length: 6070

-- 松本@二木研です。
-- 
--   bopの定義において、arityとcoarityとで異なるhidden sortを使った場合
-- の不具合を発見したので報告します。
-- 
-- (CafeOBJのバージョン)
-- CafeOBJ system Version 1.2.0 + 1.2-patch.tar.gz
-- 
--   以下のコードが問題のコードですが、このうち不具合の原因になるのは、
--
-- vvvvv Trouble vvvvv
--  bop send : NeSendAbp -> NeSendAbp
--   bop receive : NeFifo1Abp -> Abp
--  bop sent : NeSendFifo2Abp -> Abp
--  bop received : NeFifo1Abp -> NeRecAbp
-- ^^^^^ Trouble ^^^^^
-- 
-- の部分です。これがあると、inで読み込むと最終的に、
-- 
-- vvvvv
--
-- Error: The index, 1, is too large
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by CAFEOBJ-EVAL-MODULE-PROC.
-- Broken at EVAL-IMPORT-MODEXP.  Type :H for Help.
-- CHAOS>>
-- 
-- ^^^^^
--
-- となってしまいます。
--   この部分のbopをopに変更すると、inによる読み込みは正常終了します。
-- 
--
-- vvvvv 問題のコード vvvvv

mod! QUEUE [ X :: TRIV ]
{
  [ Elt < NeQueue < Queue ]

  op nullQueue : -> Queue
  op get : NeQueue -> Elt
  op put : Elt Queue -> NeQueue
  op pop : NeQueue -> Queue

  var E : Elt
  var Q : NeQueue

  eq put(E, nullQueue) = E .
  eq get(E) = E .
  eq get(put(E, Q)) = get(Q) .
  eq pop(E) = nullQueue .
  eq pop(put(E, Q)) = put(E, pop(Q)) .
}

mod* MESSAGE
{
  [ Mes ]
}

mod! MES-BOOL
{
  protecting(2TUPLE [ C1 <= view to MESSAGE { sort Elt -> Mes },
                      C2 <= view to BOOL { sort Elt -> Bool } ]
                   *{ sort 2Tuple -> MesBool })
}


mod* UNRELIABLE-FIFO-CHANNEL [ X :: TRIV ]
{
  protecting(QUEUE [X])

  *[ NeUFifo < UFifo ]*

  op  nullUFifo : -> UFifo
  bop put : Elt UFifo -> NeUFifo
  bop pop : NeUFifo -> UFifo
  bop get-queue : UFifo -> Queue
  bop get-queue : NeUFifo -> NeQueue

  var E : Elt
  var Q : UFifo
  var Q' : UFifo
  var NQ : NeUFifo

  eq get-queue(nullUFifo) = nullQueue .
  eq get-queue(put(E, Q)) = put(E, get-queue(Q)) .
  eq get-queue(pop(NQ)) = pop(get-queue(NQ)) .
  cq get-queue(Q) = get-queue(Q') if Q =*= Q' .

  trans put(E,Q) => Q .
}

mod* FIFO1
{
  protecting(UNRELIABLE-FIFO-CHANNEL [X <= view to MES-BOOL
					{ sort Elt -> MesBool } ]
	     *{ hsort UFifo -> Fifo1,
		hsort NeUFifo -> NeFifo1,
		op nullUFifo -> nullFifo1 })
}

mod* FIFO2
{
  protecting(UNRELIABLE-FIFO-CHANNEL [X <= view to BOOL
                                           { sort Elt -> Bool } ]
                                     *{ hsort UFifo -> Fifo2,
                                        hsort NeUFifo -> NeFifo2,
                                        op nullUFifo -> nullFifo2 })
}

mod* SENDER-RECEIVER
{
  protecting(QUEUE [X <= view to MESSAGE { sort Elt -> Mes }])

  *[ NeSendRec < SendRec ]*

  op srinit : -> SendRec
  bop pop : NeSendRec -> SendRec
  bop append : Mes SendRec -> NeSendRec
  bop rev : SendRec -> SendRec
  bop flag : SendRec -> Bool
  bop buf : SendRec -> Queue
  bop buf : NeSendRec -> NeQueue

  var SR : SendRec
  var NSR : NeSendRec
  var M : Mes

  eq flag(pop(NSR)) = flag(NSR) .
  eq flag(append(M, SR)) = flag(SR) .
  eq flag(rev(SR)) = not flag(SR) .
  eq buf(srinit) = nullQueue .
  eq buf(pop(NSR)) = pop(buf(NSR)) .
  eq buf(append(M, SR)) = put(M, buf(SR)) .
  eq buf(rev(SR)) = buf(SR) .
}

mod* SENDER
{
  using (SENDER-RECEIVER *{ hsort SendRec -> Sender,
                            hsort NeSendRec -> NeSender,
                            op srinit -> sender-init })
  eq flag(sender-init) = false .
}

mod* RECEIVER
{
  using (SENDER-RECEIVER *{ hsort SendRec -> Receiver,
                            hsort NeSendRec -> NeReceiver,
                            op srinit -> rec-init })
  eq flag(rec-init) = true .
}

mod* ABP
{
  protecting (SENDER)
  protecting (RECEIVER)
  protecting (FIFO1)
  protecting (FIFO2)

  *[ NeSendAbp NeRecAbp NeFifo1Abp NeFifo2Abp < Abp ]*
  *[ NeSendFifo2Abp < NeSendAbp]*
  *[ NeSendFifo2Abp < NeFifo2Abp ]*

-- the components of the system

  op sender : Abp -> Sender
  op sender : NeSendAbp -> NeSender
  op sender : NeSendFifo2Abp -> NeSender

  op receiver : Abp -> Receiver
  op receiver : NeRecAbp -> NeReceiver

  op fifo1 : Abp -> Fifo1
  op fifo1 : NeFifo1Abp -> NeFifo1

  op fifo2 : Abp -> Fifo2
  op fifo2 : NeFifo2Abp -> NeFifo2

-- methods

-- vvvvv Trouble vvvvv
  bop send : NeSendAbp -> NeSendAbp
  bop receive : NeFifo1Abp -> Abp
  bop sent : NeSendFifo2Abp -> Abp
  bop received : NeFifo1Abp -> NeRecAbp
-- ^^^^^ Trouble ^^^^^

-- the attributes are those of the components

  var A : Abp
  var NSA : NeSendAbp
  var NF1A : NeFifo1Abp
  var NSF2A : NeSendFifo2Abp
  var S : Sender
  var R : Receiver
  var F1 : Fifo1
  var F2 : Fifo2

**> equations for "send" method

  eq sender(send(NSA)) = sender(NSA) .
  eq fifo1(send(NSA)) =
     put(<< get(buf(sender(NSA))); flag(sender(NSA)) >>, fifo1(NSA)) .
  eq receiver(send(NSA)) = receiver(NSA) .
  eq fifo2(send(NSA)) = pop(fifo2(NSA)) .

**> equations for "receive" method

  eq sender(receive(NF1A)) = sender(NF1A) .
  eq fifo1(receive(NF1A)) = pop(fifo1(NF1A)) .
  eq receiver(receive(NF1A)) = receiver(NF1A) .
  eq fifo2(receive(NF1A)) = put(flag(receiver(NF1A)), fifo2(NF1A)) .

**> equations for "sent" method

  eq sender(sent(NSF2A)) = pop(rev(sender(NSF2A))) .
  eq fifo1(sent(NSF2A)) =  fifo1(NSF2A) .
  eq receiver(sent(NSF2A)) = receiver(NSF2A) .
  eq fifo2(sent(NSF2A)) = pop(fifo2(NSF2A)) .

**> equations for "received" method

  eq sender(received(NF1A)) = sender(NF1A) .
  eq fifo1(received(NF1A)) = pop(fifo1(NF1A)) .
  eq receiver(received(NF1A)) =
     append(1* get(get-queue(fifo1(NF1A))), rev(receiver(NF1A))) .
  eq fifo2(received(NF1A)) = fifo2(NF1A) .
}

-- ^^^^^ 問題のコード ^^^^^

-- 
-- 北陸先端科学技術大学院大学 情報科学研究科 情報システム学専攻
-- 言語設計学講座 二木研究室 博士前期課程 2年 在学中
-- （株）PFU 研究所 第4研究室
-- 松本 充広 mitihiro@jaist.ac.jp / michi@pfu.co.jp
eof

