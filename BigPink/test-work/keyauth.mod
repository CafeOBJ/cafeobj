-- Return-Path: amori@jaist.ac.jp
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.8.8+2.7Wbeta7/3.4W-sra) with ESMTP id JAA07099 for <sawada@sras75.sra.co.jp>; Sat, 17 Jun 2000 09:11:29 +0900 (JST)
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id JAA19805
-- 	for <sawada@srasva.sra.co.jp>; Sat, 17 Jun 2000 09:11:13 +0900 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id JAA00283
-- 	for <sawada@sra.co.jp>; Sat, 17 Jun 2000 09:11:12 +0900 (JST)
-- Received: from mail.jaist.ac.jp (mex.jaist.ac.jp [150.65.7.20])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id JAA05491
-- 	for <sawada@sra.co.jp>; Sat, 17 Jun 2000 09:11:22 +0900 (JST)
-- Received: from localhost (localhost [127.0.0.1]) by mail.jaist.ac.jp (3.7W-jaist_mail) with ESMTP id JAA11095 for <sawada@sra.co.jp>; Sat, 17 Jun 2000 09:11:18 +0900 (JST)
-- To: sawada@sra.co.jp
-- Subject: PigNose
-- Message-Id: <20000617091934P.amori@jaist.ac.jp>
-- Date: Sat, 17 Jun 2000 09:19:34 +0900
-- From: Akira Mori <amori@jaist.ac.jp>
-- X-Dispatcher: imput version 980905(IM100)
-- Mime-Version: 1.0
-- Content-Type: Text/plain; charset=iso-2022-jp
-- Lines: 279
-- Content-Length: 9440

-- 澤田さん，こんにちは．meta-paramodulation はうまく使えているようです．
-- ただ，私の使い方だと

--   ax X = a -> Q(X) = P(X) .

-- みたいに，直接述語間の等式を書いていますので，

--   ev (setq *elim-tf-in-axioms* nil)

-- の設定はあまり関係ないようです．

-- で，ちょっと質問があります．Needham-Schroeder の公開鍵プロトコルの検証，
-- というかプロトコルのエラー探索がかなりいいところまで来たのですが，
-- PigNose の動きが妙に遅いのでちょっと調べて頂きたいのです．以下に添付の
-- 例を実行すると，あとバックトラック数回で反駁できるところまで来るのです
-- が，途中で節の導出がものすごく遅くなって，最終的に私のラップトップだと

--   mmap old 'from' semispace: Cannot allocate memory

-- などというエラーで acl が落ちてしまいます．感じでは paramodulation を
-- 見付けるときの変数束縛のあたりで手間取っているような気もしますが，詳し
-- くは分りません．ひょっとすると，meta-demod や meta-paramod がボトルネッ
-- クになっている可能性もあります．ちょっと調べていただけませんか．お願い
-- します．

-- この例はほんとに難しくて苦労させられているのですが，以下の例の反駁がで
-- きたら，認証プロトコルのモデル検査が，エラー発見も含めて全部自動化でき
-- るはずなので，けっこうな killer application になると期待しています．

-- あ，そうそう大事なことを言い忘れていました．BigPink/codes/clause.lisp 
-- の sort-literals の定義で :less を :greater に変えています．
-- sort-literals って探索に影響しますよね．この辺の制御もすごくデリケート
-- なので，なにかいい方法がないか考えています．

-- 森 彰

-- ----------------------------------------------------------------------------
-- Needham-Schroeder Public Key Authentication Protocol
-- Correctness verifivation and flaw detection
-- by Akira Mori 17 June 2000

require fopl

mod* DATA {
  protecting(FOPL-CLAUSE)
  [ Nonce Agent ]
}

mod* TEXT {
  protecting(DATA)
  [ Txt ]
  op contact : Nonce Agent -> Txt
  op respond : Nonce Nonce -> Txt
  op confirm : Nonce -> Txt
  pred contain : Txt Nonce { meta-demod} -- { decidable }
  vars M N M1 N1 : Nonce
  vars A B : Agent
--  ax \A[T:Txt] (\E[N:Nonce]\E[A:Agent] T = contact(N,A)) |
--             (\E[M:Nonce]\E[N:Nonce] T = respond(M,N)) |
--               (\E[N:Nonce] T = confirm(N)) .

  ax ~(contact(N,A) = respond(M,N1)) .
  ax ~(contact(N,A) = confirm(N1)) .
  ax ~(respond(M,N) = confirm(N1)) .

  ax (contact(N,A) = contact(M,B)) -> (N = M & A = B) .
  ax (respond(M,N) = respond(M1,N1)) -> (M = M1 & N = N1) .
  ax (confirm(N) = confirm(M)) -> (M = N) .

  ax contain(contact(N,A),M) -> (M = N) .
  ax contain(respond(N,N1),M) -> (M = N | M = N1) .
  ax contain(confirm(N),M) -> (M = N) .

  ax contain(contact(M,A),M) .
  ax contain(respond(M,N),M) .
  ax contain(respond(N,M),M) .
  ax contain(confirm(M),M) .

}

mod! MESSAGE {
  protecting(TEXT)
  [ PKey Msg ]
  op pkey : Agent -> PKey
  op encrypt : PKey Txt -> Msg
  vars A B A1 B1 : Agent
  vars M N M1 N1 : Nonce
  vars K K1 K2 : PKey
  vars T T1 T2 : Txt
  vars S S1 S2 : Msg
--  ax \A[K:PKey]\E[A:Agent] K = pkey(A) .
--  ax (pkey(A) = pkey(B)) -> (A = B) .
--  ax \A[S:Txt]\E[K:PKey]\E[T:Txt] S = encrypt(K,T) .
--  ax \A[S:Msg]\E[A:Agent]\E[T:Txt] S = encrypt(pkey(A),T) .

--  ax (encrypt(K1,T1) = encrypt(K2,T2)) -> (K1 = K2 & T1 = T2) .

  ax (encrypt(pkey(A),T1) = encrypt(pkey(B),T2)) -> (A = B & T1 = T2) .
}

mod* NSPK {
  protecting(MESSAGE)

  *[ Protocol ]*

  pred said : Agent Agent Msg Protocol {meta-demod} --  meta{decidable}
  pred used : Nonce Protocol {meta-demod} -- { decidable }
  pred exposed : Nonce Protocol {meta-demod} -- { decidable }
  op trans : Msg Protocol -> Protocol
  op init : -> Protocol   
  op spy : -> Agent

  vars M N NA NB : Nonce   vars A B C D X Y : Agent   var P : Protocol
  vars S S1 S2 : Msg   vars K K1 K2 : PKey   vars T T1 : Txt

  ax ~(used(N,init)) .
  ax ~(said(A,B,S,init)) . 
--  ax said(A,B,S,init) -> said(A,B,S,trans(S1,P)) . 
  ax used(N,P) -> used(N,trans(S,P)) .

  ax ~(S = S1) -> said(A,B,S,trans(S1,P)) = said(A,B,S,P) .

  -- contact
  ax ~(used(NA,P)) ->
     said(A,B,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) & used(NA,trans(encrypt(pkey(B),contact(NA,A)),P)) .

  ax used(NA,P) & ~(A = spy) ->
     said(A,B,encrypt(pkey(B),contact(NA,A)),P) = said(A,B,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) .

  ax used(NA,P) & ~(exposed(NA,P)) ->
     said(spy,B,encrypt(pkey(B),contact(NA,A)),P) = said(spy,B,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) .

  ax exposed(NA,P) -> said(spy,C,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) .

  ax ~(C = spy) & ~(A = C & B = D) -> said(C,D,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) = said(C,D,encrypt(pkey(B),contact(NA,A)),P) .

  ax ~(exposed(NA,P)) & ~(A = spy & B = D) -> said(spy,D,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) = said(spy,D,encrypt(pkey(B),contact(NA,A)),P) .

  ax ~(N = NA) -> used(N,trans(encrypt(pkey(B),contact(NA,A)),P)) = used(N,P) .


  -- respond
  ax ~(used(NB,P)) & 
     (\E[X:Agent] said(X,B,encrypt(pkey(B),contact(NA,A)),P)) -> 
     said(B,A,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) & used(NB,trans(encrypt(pkey(A),respond(NA,NB)),P)) .

  ax ~(used(NB,P)) & ~(B = spy) &
     (\A[X:Agent] ~(said(X,B,encrypt(pkey(B),contact(NA,A)),P))) -> 
     said(B,A,encrypt(pkey(A),respond(NA,NB)),P) = said(B,A,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) & ~(used(NB,trans(encrypt(pkey(A),respond(NA,NB)),P))) .

  ax used(NB,P) & ~(B = spy) ->
     said(B,A,encrypt(pkey(A),respond(NA,NB)),P) = said(B,A,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) .

  ax exposed(NA,P) & exposed(NB,P) ->
     said(spy,B,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) .

  ax ~(C = spy) & ~(B = D) -> said(C,D,encrypt(pkey(B),respond(NA,NB)),trans(encrypt(pkey(B),respond(NA,NB)),P)) = said(C,D,encrypt(pkey(B),respond(NA,NB)),P) .

  ax ~(exposed(NA,P) & exposed(NB,P)) & ~(B = D) -> said(spy,D,encrypt(pkey(B),respond(NA,NB)),trans(encrypt(pkey(B),respond(NA,NB)),P)) = said(spy,D,encrypt(pkey(B),respond(NA,NB)),P) .

  ax ~(N = NB) -> used(N,trans(encrypt(pkey(B),respond(NA,NB)),P)) = used(N,P) .


  -- confirm
  ax said(A,B,encrypt(pkey(B),contact(NA,A)),P) &
     said(X,A,encrypt(pkey(A),respond(NA,NB)),P) ->
     said(A,B,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) .

  ax ~(A = spy) &
     ~(\E[X:Agent]\E[NA:Nonce]
       said(A,B,encrypt(pkey(B),contact(NA,A)),P) &
       said(X,A,encrypt(pkey(A),respond(NA,NB)),P)) ->
     said(A,B,encrypt(pkey(B),confirm(NB)),P) = said(A,B,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) .

  ax exposed(NB,P) ->
     said(spy,C,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) .

  ax ~(C = spy) & ~(B = D) -> said(C,D,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) = said(C,D,encrypt(pkey(B),confirm(NB)),P) .

  ax ~(exposed(NB,P)) & ~(B = D) -> said(spy,D,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) = said(spy,D,encrypt(pkey(B),confirm(NB)),P) .

  ax used(N,P) = used(N,trans(encrypt(pkey(B),confirm(NB)),P)) .


  -- Exposed Nonces (to Spy)
  ax ~(X = spy) -> exposed(N,P) = exposed(N,trans(encrypt(pkey(X),T),P)) .

  ax contain(T,N) -> exposed(N,trans(encrypt(pkey(spy),T),P)) .

  ax ~(contain(T,N)) -> exposed(N,P) = exposed(N,trans(encrypt(pkey(spy),T),P)) .

}

mod* PROOF {

protecting(NSPK)

ops a b : -> Agent .
ops x y : -> Agent .
ops m n : -> Nonce .
op p : -> Protocol .

vars X Y A B : Agent .
vars NA NB : Nonce .
vars S S1 : Msg .
vars P R : Protocol .

pred P : Protocol .
#define P(R:Protocol) ::= said(x,y,encrypt(pkey(y),contact(n,x)),R) |
                          ~(said(y,x,encrypt(pkey(x),respond(n,m)),R)) |
			  ~(said(spy,y,encrypt(pkey(y),confirm(m)),R)) .

ax \A[B1:Agent]\A[B2:Agent]\A[B3:Agent]\A[B4:Agent]\A[B5:Agent]\A[T1:Txt]\A[T2:Txt]\A[T3:Txt]\A[T4:Txt]\A[T5:Txt] P(trans(encrypt(pkey(B5),T5),trans(encrypt(pkey(B4),T4),trans(encrypt(pkey(B3),T3),trans(encrypt(pkey(B2),T2),trans(encrypt(pkey(B1),T1),init)))))) .  -- should cause contradiction

ax ~(m = n) .
ax ~(x = spy) .
ax ~(y = spy) .
ax ~(x = y) .

}

open PROOF .

db reset
option reset

flag(process-input, on)
flag(print-kept, off)
flag(print-new-demod, off)
flag(print-back-demod, off)
flag(print-back-sub, off)
flag(control-memory, off)
param(max-sos, 30000) .
param(pick-given-ratio, 1) .
param(stats-level, 1) .
param(max-seconds, 86400) .
flag(kb, on)
flag(para-from, off)
flag(para-into, on)
flag(para-from-right, off)
flag(para-into-right, off)
flag(para-from-vars, off)
flag(eq-units-both-ways, on)
flag(dynamic-demod-all, on)
flag(dynamic-demod, on)
flag(order-eq, on)
flag(back-demod, on)
flag(lrpo, on)
flag(hyper-res, off)
flag(unit-deletion, on)
flag(factor, on)

-- flag(prop-res, on)
-- flag(neg-hyper-res, on)
-- flag(order-hyper, on)
flag(binary-res, on)
-- flag(no-new-demod, on)
-- flag(para-into-vars, on)

-- flag(auto3, on)

flag(print-stats,on)
flag(universal-symmetry,on)
-- param(max-weight,300)
param(max-proofs,1)

flag(input-sos-first,on)
-- flag(sos-queue,on)
-- flag(sos-stack,on)
flag(sort-literals,on)
-- flag(unify-heavy,on)
-- flag(para-skip-skolem,on)
-- flag(para-from-units-only,on)

sos = { 1 }

ev (setq *elim-tf-in-axioms* nil)

resolve .

close
**
eof
**
$Id:
