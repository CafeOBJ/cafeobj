-- Return-Path: amori@jaist.ac.jp 
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id XAA21348 for <sawada@sras75.sra.co.jp>; Sat, 13 Nov 1999 23:15:32 +0900
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id XAA12715
-- 	for <sawada@srasva.sra.co.jp>; Sat, 13 Nov 1999 23:18:54 +0859 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id XAA28689
-- 	for <sawada@sra.co.jp>; Sat, 13 Nov 1999 23:19:12 +0900 (JST)
-- Received: from mail.jaist.ac.jp (mex.jaist.ac.jp [150.65.7.20])
-- 	by sraigw.sra.co.jp (8.8.7/3.7W-sraigw) with ESMTP id XAA08011
-- 	for <sawada@sra.co.jp>; Sat, 13 Nov 1999 23:19:06 +0900 (JST)
-- Received: from localhost (jaist-gate24 [150.65.30.54]) by mail.jaist.ac.jp (3.7W-jaist_mail) with ESMTP id XAA10082; Sat, 13 Nov 1999 23:19:04 +0900 (JST)
-- To: sawada@sra.co.jp, Akishi.Seo@unisys.co.jp
-- Subject: ICSE paper
-- Message-Id: <19991113232053T.amori@jaist.ac.jp>
-- Date: Sat, 13 Nov 1999 23:20:53 +0900
-- From: Akira Mori <amori@jaist.ac.jp>
-- X-Dispatcher: imput version 980905(IM100)
-- Mime-Version: 1.0
-- Lines: 62
-- Content-Type: Text/plain; charset=iso-2022-jp
-- Content-Length: 2121

-- 澤田さん，瀬尾さんご苦労さまでした．

-- ICSE'2000 の論文はなんとかまともなものを提出しました．時間がなかったの
-- できつかったです．

-- 論文を

--   http://caraway.jaist.ac.jp/ipa/member/{icse2000.ps, icse2000.ps.gz}

-- においておきましたので覗いて見て下さい．プリントアウトせずにそのままファ
-- イル転送で送るという画期的なことをしてしまいました．もうちょっとちゃん
-- としたかったですが，まあまあ書きたいことは書いたのでよしとします．

-- To 澤田さん

-- 以下のモジュールをロードして sigmatch して check refinement するとおか
-- しくなります．ちょっと見てもらえますか．来週の火曜に電総研大阪で話する
-- んですが，ついでにデモもするつもりでいます．Cousot とかも来るようなの
-- で，ちょっとアピールできるといいですね．また急にむちゃなお願いをするか
-- も知れませんが，適当に無視して下さい．

-- それでは．

-- 森 彰
 
mod* SENDER {
  *[ Sender ]*  [ Data ]
  bop bit : Sender -> Bool
  bop val : Sender -> Data
  bop in : Data Bool Sender -> Sender
  op init : -> Sender
  var D : Data   var B : Bool   var S : Sender
  eq bit(init) = true .   -- valid initial state
  ceq val(in(D,B,S)) = D if bit(S) == B . -- new data for right ack
  ceq bit(in(D,B,S)) = not bit(S) if bit(S) == B . -- alternates bit
  bceq in(D,B,S) = S if bit(S) =/= B .  -- stays put for wrong ack
}

mod* RECEIVER {
  *[ Receiver ]*  [ Data ]
  bop bit : Receiver -> Bool
  bop val : Receiver -> Data
  bop get : Data Bool Receiver -> Receiver
  op init : -> Receiver
  var D : Data   var B : Bool   var R : Receiver
  eq bit(init) = true .   -- valid initial state
  ceq val(get(D,B,R)) = D if bit(R) =/= B . -- output value
  ceq bit(get(D,B,R)) = not bit(R) if bit(R) =/= B . -- alternates bit
  bceq get(D,B,R) = R if bit(R) == B . -- stays put for wrong bit
}


eof

CafeOBJ> sigmatch (SENDER) to (RECEIVER)
(V#1)
CafeOBJ> check refinement V#1
Error: Attempt to take the cdr of
       #<Printer Error, obj=#x200009: #<simple-error @ #x2084f7a2>>
       which is not listp.
  [condition type: simple-error]

[changing package from "COMMON-LISP-USER" to "CHAOS"]
[1] CHAOS(1): 

$Id:

