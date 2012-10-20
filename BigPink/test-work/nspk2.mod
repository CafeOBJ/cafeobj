-- Return-Path: amori@jaist.ac.jp
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.8.8+2.7Wbeta7/3.4W-sra) with ESMTP id OAA09021 for <sawada@sras75.sra.co.jp>; Wed, 21 Jun 2000 14:47:15 +0900 (JST)
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id OAA06615
-- 	for <sawada@srasva.sra.co.jp>; Wed, 21 Jun 2000 14:46:57 +0859 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id OAA26479
-- 	for <sawada@sra.co.jp>; Wed, 21 Jun 2000 14:46:56 +0859 (JST)
-- Received: from mail.jaist.ac.jp (mex.jaist.ac.jp [150.65.7.20])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id OAA11165
-- 	for <sawada@sra.co.jp>; Wed, 21 Jun 2000 14:47:10 +0900 (JST)
-- Received: from kite.jaist.ac.jp (localhost [127.0.0.1]) by mail.jaist.ac.jp (3.7W-jaist_mail) with ESMTP id OAA09755 for <sawada@sra.co.jp>; Wed, 21 Jun 2000 14:47:09 +0900 (JST)
-- Received: from localhost
-- 	([127.0.0.1] helo=kite.jaist.ac.jp ident=amori)
-- 	by kite.jaist.ac.jp with esmtp (Exim 3.12 #1 (Debian))
-- 	id 134dIj-0001LG-00
-- 	for <sawada@sra.co.jp>; Wed, 21 Jun 2000 14:43:49 +0900
-- To: sawada@sra.co.jp
-- Subject: bug1.mod
-- Date: Wed, 21 Jun 2000 14:43:49 +0900
-- From: Akira Mori <amori@jaist.ac.jp>
-- Message-Id: <E134dIj-0001LG-00@kite.jaist.ac.jp>
-- Content-Length: 7731

-- Needham-Schroeder Public Key Authentication Protocol
-- Flaw detection
-- by Akira Mori 19 June 2000

require fopl

mod* DATA {
  protecting(FOPL-CLAUSE)
  [ AId Nonce Agent ]
  op agent : AId -> Agent
  op spy : -> Agent
  ops p q : -> AId
  ops m n : -> Nonce
  vars M N : AId
  ax (agent(M) = agent(N)) <-> (M = N) .
  ax ~(agent(M) = spy) .
  ax ~(p = q) .
  ax ~(m = n) .
}



mod* TEXT {
  protecting(DATA)
  [ Txt ]
  op contact : Nonce Agent -> Txt
  op respond : Nonce Nonce -> Txt
  op confirm : Nonce -> Txt
  vars M N M1 N1 : Nonce
  vars A B : Agent

  ax ~(contact(N,A) = confirm(N1)) .
  ax ~(contact(N,A) = respond(M,N1)) .
  ax ~(respond(M,N) = confirm(N1)) .

  ax (contact(N,A) = contact(M,B)) -> (N = M & A = B) .
  ax (respond(M,N) = respond(M1,N1)) -> (M = M1 & N = N1) .
  ax (confirm(N) = confirm(M)) -> (M = N) .
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

  ax (encrypt(pkey(A),T1) = encrypt(pkey(B),T2)) -> (A = B & T1 = T2) .
}

mod* NSPK {
  protecting(MESSAGE)

  *[ Protocol ]*

  pred said : Agent Agent Msg Protocol {meta-demod}
  pred used : Nonce Protocol { meta-demod }
  pred exposed : Nonce Protocol { meta-demod }
  op trans : Msg Protocol -> Protocol
  op init : -> Protocol   

  vars M N NA NB : Nonce   vars A B C D X Y : Agent   var P : Protocol
  vars S S1 S2 : Msg   vars K K1 K2 : PKey   vars T T1 : Txt

  ax ~(used(N,init)) .
  ax ~(exposed(N,init)) .
  ax ~(said(A,B,S,init)) . 
--  ax said(A,B,S,P) -> said(A,B,S,trans(S1,P)) . 
  ax used(N,P) -> used(N,trans(S,P)) .
  ax exposed(N,P) -> exposed(N,trans(S,P)) .

  ax ~(said(A,A,S,P)) .

--  ax ~(S = S1) -> said(A,B,S,trans(S1,P)) = said(A,B,S,P) .

  ax ~(X = spy) -> exposed(N,trans(encrypt(pkey(X),T),P)) = exposed(N,P) .


  -- contact
  ax ~(used(NA,P)) & ~(A = B) ->
     said(A,B,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) & used(NA,trans(encrypt(pkey(B),contact(NA,A)),P)) .

  ax ~(used(NA,P)) -> exposed(NA,trans(encrypt(pkey(spy),contact(NA,A)),P)) .
  ax used(NA,P) & ~(exposed(NA,P)) -> ~(exposed(NA,trans(encrypt(pkey(spy),contact(NA,A)),P))) . 

  ax used(NA,P) & ~(A = spy) ->
     said(A,B,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) = said(A,B,encrypt(pkey(B),contact(NA,A)),P) .

  ax used(NA,P) & ~(exposed(NA,P)) ->
     said(spy,B,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) = said(spy,B,encrypt(pkey(B),contact(NA,A)),P) .

  ax exposed(NA,P) & ~(C = spy) -> said(spy,C,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) .

  ax ~(C = spy) & ~(A = C & B = D) -> said(C,D,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) = said(C,D,encrypt(pkey(B),contact(NA,A)),P) .

  ax ~(exposed(NA,P)) & ~(A = spy & B = D) -> said(spy,D,encrypt(pkey(B),contact(NA,A)),trans(encrypt(pkey(B),contact(NA,A)),P)) = said(spy,D,encrypt(pkey(B),contact(NA,A)),P) .

  ax ~(N = NA) -> used(N,trans(encrypt(pkey(B),contact(NA,A)),P)) = used(N,P) .


  -- respond
  ax ~(used(NB,P)) & ~(B = A) &
     (\E[X:Agent] said(X,B,encrypt(pkey(B),contact(NA,A)),P)) -> 
     said(B,A,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) & used(NB,trans(encrypt(pkey(A),respond(NA,NB)),P)) .

  ax ~(used(NB,P)) &
     (\E[X:Agent] said(X,B,encrypt(pkey(B),contact(NA,spy)),P)) -> 
     exposed(NA,trans(encrypt(pkey(spy),respond(NA,NB)),P)) &
     exposed(NB,trans(encrypt(pkey(spy),respond(NA,NB)),P)) .

  ax (used(NB,P) |
     (\A[X:Agent] ~(said(X,B,encrypt(pkey(B),contact(NA,spy)),P)))) &
     ~(exposed(NB,P)) -> ~(exposed(NB,trans(encrypt(pkey(spy),respond(NA,NB)),P))) .

  ax (used(NB,P) |
     (\A[X:Agent] ~(said(X,B,encrypt(pkey(B),contact(NA,spy)),P)))) &
     ~(exposed(NA,P)) -> ~(exposed(NA,trans(encrypt(pkey(spy),respond(NA,NB)),P))) .

  ax ~(used(NB,P)) & ~(B = spy) &
     (\A[X:Agent] ~(said(X,B,encrypt(pkey(B),contact(NA,A)),P))) -> 
     said(B,A,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) = said(B,A,encrypt(pkey(A),respond(NA,NB)),P) & ~(used(NB,trans(encrypt(pkey(A),respond(NA,NB)),P))) .

  ax used(NB,P) & ~(B = spy) ->
     said(B,A,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) = said(B,A,encrypt(pkey(A),respond(NA,NB)),P) .

  ax exposed(NA,P) & exposed(NB,P) & ~(B = spy) ->
     said(spy,B,encrypt(pkey(A),respond(NA,NB)),trans(encrypt(pkey(A),respond(NA,NB)),P)) .

  ax ~(C = spy) & ~(B = D) -> said(C,D,encrypt(pkey(B),respond(NA,NB)),trans(encrypt(pkey(B),respond(NA,NB)),P)) = said(C,D,encrypt(pkey(B),respond(NA,NB)),P) .

  ax ~(exposed(NA,P) & exposed(NB,P)) & ~(B = D) -> said(spy,D,encrypt(pkey(B),respond(NA,NB)),trans(encrypt(pkey(B),respond(NA,NB)),P)) = said(spy,D,encrypt(pkey(B),respond(NA,NB)),P) .

  ax ~(N = NB) -> used(N,trans(encrypt(pkey(B),respond(NA,NB)),P)) = used(N,P) .


  -- confirm
  ax said(A,B,encrypt(pkey(B),contact(NA,A)),P) &
     said(X,A,encrypt(pkey(A),respond(NA,NB)),P) & ~(A = B) ->
     said(A,B,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) .

  ax said(A,spy,encrypt(pkey(spy),contact(NA,A)),P) &
     said(X,A,encrypt(pkey(A),respond(NA,NB)),P) ->
     exposed(NB,trans(encrypt(pkey(spy),confirm(NB)),P)) .

  ax ~(\E[X:Agent]\E[NA:Nonce]
       said(A,spy,encrypt(pkey(spy),contact(NA,A)),P) &
       said(X,A,encrypt(pkey(A),respond(NA,NB)),P)) &
     ~(exposed(NB,P)) -> ~(exposed(NB,trans(encrypt(pkey(spy),confirm(NB)),P))) .

  ax ~(A = spy) & 
     ~(\E[X:Agent]\E[NA:Nonce]
       said(A,B,encrypt(pkey(B),contact(NA,A)),P) &
       said(X,A,encrypt(pkey(A),respond(NA,NB)),P)) ->
     said(A,B,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) = said(A,B,encrypt(pkey(B),confirm(NB)),P) .

  ax exposed(NB,P) & ~(C = spy) ->
     said(spy,C,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) .

  ax ~(C = spy) & ~(B = D) -> said(C,D,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) = said(C,D,encrypt(pkey(B),confirm(NB)),P) .

  ax ~(exposed(NB,P)) & ~(B = D) -> said(spy,D,encrypt(pkey(B),confirm(NB)),trans(encrypt(pkey(B),confirm(NB)),P)) = said(spy,D,encrypt(pkey(B),confirm(NB)),P) .

  ax used(N,trans(encrypt(pkey(B),confirm(NB)),P)) = used(N,P) .
}

mod* PROOF {

protecting(NSPK)

ops m n : -> Nonce .
ops x y : -> Agent .

goal \E[B1:Agent]\E[T1:Txt] said(x,y,encrypt(pkey(y),respond(m,n)),trans(encrypt(pkey(B1),T1),init)) .

}

open PROOF .

db reset
option reset

flag(process-input, on)
-- flag(print-kept, off)
flag(print-kept, on)
flag(print-new-demod, off)
flag(print-back-demod, off)
flag(print-back-sub, on)
flag(control-memory, on)
param(max-sos, 30000) .
param(pick-given-ratio, 8) .
param(stats-level, 4) .
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
flag(very-verbose,on)
-- flag(no-new-demod, on)
-- flag(para-into-vars, on)

-- flag(auto3, on)

flag(print-stats,on)
flag(universal-symmetry,on)
-- param(max-weight,150)
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
$Id
