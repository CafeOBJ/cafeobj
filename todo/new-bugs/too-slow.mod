-- Return-Path: dlucanu@info.uaic.ro 
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id XAA15885 for <sawada@sras75.sra.co.jp>; Fri, 12 Feb 1999 23:30:46 +0900
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id XAA06991
-- 	for <sawada@srasva.sra.co.jp>; Fri, 12 Feb 1999 23:31:23 +0900 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id XAA09297
-- 	for <sawada@sra.co.jp>; Fri, 12 Feb 1999 23:31:35 +0900 (JST)
-- Received: from orion.uaic.ro (orion.uaic.ro [193.226.23.1])
-- 	by sraigw.sra.co.jp (8.8.7/3.6Wbeta7-sraigw) with ESMTP id XAA01978
-- 	for <sawada@sra.co.jp>; Fri, 12 Feb 1999 23:31:32 +0900 (JST)
-- Received: from thor.infoiasi.ro (root@thor.info.uaic.ro [193.231.30.193])
-- 	by orion.uaic.ro (8.8.7/8.8.7) with ESMTP id OAA28886
-- 	for <sawada@sra.co.jp>; Fri, 12 Feb 1999 14:42:41 +0200
-- Received: from info.uaic.ro (IDENT:dlucanu@lucanu.info.uaic.ro [193.231.30.218])
-- 	by thor.infoiasi.ro (8.9.2/8.9.2) with ESMTP id QAA13174
-- 	for <sawada@sra.co.jp>; Fri, 12 Feb 1999 16:31:44 +0200 (EET)
-- Sender: dlucanu@infoiasi.ro
-- Message-ID: <36C458EA.2A90A27E@info.uaic.ro>
-- Date: Fri, 12 Feb 1999 16:38:02 +0000
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- Organization: University "A.I.Cuza",  Faculty of Computer Science
-- X-Mailer: Mozilla 4.04 [en] (X11; I; Linux 2.0.33 i586)
-- MIME-Version: 1.0
-- To: Toshimi Sawada <sawada@sra.co.jp>
-- Subject: sorry, wrong file attached
-- Content-Type: multipart/mixed; boundary="------------41BEF9B28048CB33146F26EC"
-- Content-Length: 11535

-- This is a multi-part message in MIME format.
-- --------------41BEF9B28048CB33146F26EC
-- Content-Type: text/plain; charset=us-ascii
-- Content-Transfer-Encoding: 7bit

-- Dear Toshimi,

-- By a regretable mistake, I attached a wrong file (it includes much more
-- you need and a different test). Now I attached the right file.

-- Best regards,
-- Dorel.
-- -- 
-- =========================================
-- Dorel Lucanu
-- Universitatea "A.I.Cuza"
-- Facultatea de Informatica
-- str. Berthelot 16
-- 6600 Iasi, Romania

-- e-mail: dlucanu@infoiasi.ro
-- home page: http://www.infoiasi.ro/~dlucanu/
-- tel: home       40 32 156487
--      office     40 32 146141
--      department 40 32 216560
-- =========================================
-- --------------41BEF9B28048CB33146F26EC
-- Content-Type: text/plain; charset=us-ascii; name="rabp.mod"
-- Content-Transfer-Encoding: 7bit
-- Content-Disposition: inline; filename="rabp.mod"

mod* DATA { [ Data ] }

mod* TRIV+ { pr(TRIV) [Elt < Elt+] op err : -> Elt+ }

mod* ILIST[X :: TRIV] {
  [ IList ]
  op head_ : IList -> Elt
  op tail_ : IList -> IList
}

mod! FLIST[X :: TRIV] {
  [NeFList < FList]
  op [nil] : -> FList
  op head_ : NeFList -> Elt
  op tail_ : NeFList -> FList
  op [_]_ : Elt FList -> NeFList 
  var L : FList
  var E : Elt
  eq head([E] L) = E .
  eq tail([E] L) = L .
}

mod! DATA-BOOL {
  protecting (2TUPLE (C1 <= view to DATA {sort Elt -> Data},
		      C2 <= view to BOOL {sort Elt -> Bool})
	      * {sort 2Tuple -> Data-Bool})
  [Data-Bool < Data-Bool+]
  op << err ; false >> : -> Data-Bool+
}

mod! BOOL+ { [Bool+]  [Bool < Bool+] op err : -> Bool+ }



-- a new version (8.02.99)


mod! EVENTS-SR {
  [EventSR]
  ops SEND REC : -> EventSR
  op next_ : EventSR -> EventSR
  eq next SEND = REC .
  eq next REC = SEND .
  eq next next E:EventSR = E .
}


-- the sender and receiver

mod* SENDER/RECEIVER (X :: TRIV, Y :: TRIV) {
  protecting(EVENTS-SR)

  *[ SenderReceiver ]*
  -- operators for scenario
  op m : SenderReceiver -> SenderReceiver {coherent}
  op event_ : SenderReceiver -> EventSR
  -- additional operators
  op init : -> SenderReceiver
  op receive : SenderReceiver Elt.Y -> SenderReceiver {coherent}
  bop rcvd-data_ : SenderReceiver -> Elt.Y
  bop flag_ : SenderReceiver -> Bool

  var SR : SenderReceiver
  var E : Elt.Y
  -- equations for scenario
  eq event m(SR) = next event SR .
  eq event receive(SR, E) = event SR .
  -- equations for flag
  ceq flag m(SR) = flag(SR) if event SR == SEND .
  eq flag receive(SR, E) = flag SR .
  -- equations for rcvd-data
  eq rcvd-data receive(SR, E) = E .
  eq rcvd-data m(SR) = rcvd-data SR .
}

mod* SENDER {
  protecting (SENDER/RECEIVER(X <= view to DATA-BOOL {sort Elt -> Data-Bool}
			      Y <= view to BOOL {sort Elt -> Bool}
			      )*{hsort SenderReceiver -> Sender
				 op init -> init-S })
  protecting(ILIST(X <= view to DATA {sort Elt -> Data}))
  
  bop sndng-list _ : Sender -> IList 
  var S : Sender
  var B : Bool

  eq event init-S = SEND .

  eq flag init-S  = true .
  ceq flag m(S) = flag(S) 
  if event S == REC and rcvd-data m(S) == (not flag S) .
  ceq flag m(S) = not flag(S) 
  if event S == REC and rcvd-data m(S) == flag S .
  
  ceq sndng-list m(S) = sndng-list S 
    if event S == SEND or (event S == REC and rcvd-data m(S) == (not flag S)) .
  ceq sndng-list m(S) = tail(sndng-list S) 
  if event S == REC and rcvd-data m(S) == flag S .
  eq sndng-list receive(S, B) = sndng-list S .
}

mod* RECEIVER {
  protecting (SENDER/RECEIVER(X <= view to BOOL {sort Elt -> Bool},
			      Y <= view to DATA-BOOL {sort Elt -> Data-Bool}
			      )*{hsort SenderReceiver -> Receiver
				 op init -> init-R })

  protecting(FLIST(X <= view to DATA {sort Elt -> Data}))

  bop rcvd-list _ : Receiver -> FList
  var R : Receiver
  var DB : Data-Bool

  eq event init-R = REC .

  eq flag init-R = false .
  eq rcvd-list init-R = [nil] .

  ceq flag m(R) = flag R
    if event R == REC and 2* rcvd-data m(R) == flag R .
  ceq flag m(R) = not flag R 
    if event R == REC and 2* rcvd-data m(R) == (not flag R) .
  
  ceq rcvd-list m(R) = rcvd-list R 
    if event R == SEND or (event R == REC and 2* rcvd-data m(R) == flag R) .
  ceq rcvd-list m(R) = [1* rcvd-data m(R)] rcvd-list R  
    if event R == REC and 2* rcvd-data m(R) == (not flag R) .
  eq rcvd-list receive(R, DB) = rcvd-list R .
}

-- the channels

mod* UBUFFER (X :: TRIV+) {
  *[ UBuffer ]*
  op init : -> UBuffer
  bop put : UBuffer Elt -> UBuffer
  op del : UBuffer -> UBuffer {coherent}
  bop get_ : UBuffer -> Elt
  bop get_ : UBuffer -> Elt+
  bop empty?_ : UBuffer -> Bool { memo }
  bop cserr?_ : UBuffer -> Bool { memo }

  var UB : UBuffer
  var E : Elt
 
  ceq get put(UB,E) = E  if not cserr? put(UB,E) .
  ceq get UB = err if empty? UB or cserr? UB .
  eq empty? init = true .
  eq empty? del(UB) = true .
  eq empty? put(UB, E) = false .
}

mod* UCH1 {
  protecting (UBUFFER (X <= view to DATA-BOOL {sort Elt -> Data-Bool, 
					       sort Elt+ -> Data-Bool+,
					       op err -> << err ; false >>})
	      *{hsort UBuffer -> UCh1,
		op init -> init-UCH1 })
}

mod* UCH2 {
  protecting (UBUFFER (X <= view to BOOL+ {sort Elt -> Bool, sort Elt+ -> Bool+})
	      *{hsort UBuffer -> UCh2,
		op init -> init-UCH2 })
}

mod! EVENTS-ABP {
  [ Event ]
  ops SENDER RECEIVER : -> Event
}
-- ABP with reliable channels


mod* CH1 {
  protecting(UCH1)
  
  eq cserr?(put(UC:UCh1, DB:Data-Bool)) = false .
}

mod* CH2 {
  protecting(UCH2)
          
  eq cserr?(put(UC:UCh2, B:Bool)) = false .
}

mod* RABP {
  protecting (SENDER + CH1 + RECEIVER + CH2 + EVENTS-ABP)
  *[ Abp ]*
    
  op init : -> Abp
  bop m : Abp -> Abp
  ** bop event_ : Abp -> Event
  bop event_ : Abp -> Event { memo }
  -- projections on the components
  op uch1_ : Abp -> UCh1 { coherent }
  op uch2_ : Abp -> UCh2 { coherent }
  ** op sender_ : Abp -> Sender { coherent }
  op sender_ : Abp -> Sender { coherent memo }
  ** op receiver_ : Abp -> Receiver { coherent }
  op receiver_ : Abp -> Receiver { coherent memo }

  var A : Abp

  -- initial state 
  eq uch1 init = init-UCH1 .
  eq uch2 init = init-UCH2 .
  eq sender init = init-S .
  eq receiver init = init-R .

  -- projection equations
  ceq sender m(A) = m(sender A) 
  if event A == SENDER and (event sender A == SEND or cserr? uch2 A) .
  ceq sender m(A) = m(receive(sender A, get uch2 A)) 
  if event A == SENDER and (event sender A == REC) and 
    (not empty? uch2 A) and (not cserr? uch2 A) .
  ceq sender m(A) = sender A 
    if (event A == RECEIVER) or 
      (event A == SENDER) and (event sender A == REC) and (empty? uch2 A) .
  
  ceq receiver m(A) = m(receiver A) 
  if event A == RECEIVER and (event receiver A == SEND or cserr? uch1 A) .
  ceq receiver m(A) = m(receive(receiver A, get uch1 A)) 
  if (event A == RECEIVER) and (event receiver A == REC) and 
    (not empty? uch1 A) and (not cserr? uch1 A) .
  ceq receiver m(A) = receiver A 
    if (event A == SENDER) or 
       (event A == RECEIVER) and (event receiver A == REC) and (empty? uch1 A) .

  ceq uch1 m(A) = put(uch1 A, << head(sndng-list sender A) ; flag sender A >>) 
  if (event A == SENDER) and (event sender A == SEND) and (empty? uch1 A) .
  ceq uch1 m(A) = del(uch1 A) 
  if (event A == RECEIVER) and (event receiver A == REC) and (not empty? uch1 A) .
  ceq uch1 m(A) = uch1 A  
    if (event A == SENDER) and (event sender A == SEND) and (not empty? uch1 A) or
      (event A == SENDER) and (event sender A == REC) or
	(event A == RECEIVER) and (event receiver A == REC) and (empty? uch1 A) or
	  (event A == RECEIVER) and (event receiver A == SEND) .
  
  ceq uch2 m(A) = put(uch2 A, flag receiver A) 
  if (event A == RECEIVER) and (event receiver A == SEND) and (empty? uch2 A) .
  ceq uch2 m(A) = del(uch2 A) 
  if (event A == SENDER) and (event sender A == REC) and (not empty? uch2 A) .
  ceq uch2 m(A) = uch2 A 
    if (event A == RECEIVER) and (event receiver A == SEND) and (not empty? uch2 A) or
      (event A == RECEIVER) and (event receiver A == REC) or
	(event A == SENDER) and (event sender A == REC) and (empty? uch2 A) or
	  (event A == SENDER) and (event sender A == SEND) .
}


-- RABP specifies a corect solution for USRP

mod RABP-PROOF {
  pr(RABP)
  op a   : -> Abp
  ops d1 d2 : -> Data
  op b   : -> Bool
  op FL : -> FList
  op IL : -> IList
  op next_ : Event -> Event

  eq next SENDER = RECEIVER .
  eq next RECEIVER = SENDER .
  eq next next E:Event = E .

  eq event m(A:Abp) = next event A .

  eq event a = SENDER .
  eq event sender a = SEND .
  eq event receiver a = SEND .
  eq empty? uch1 a = true .
  eq empty? uch2 a = true .
  eq head IL  = d1 .
  eq head tail IL = d2 .

  eq not not B:Bool = B .
}

open RABP-PROOF .
eq sndng-list sender a = IL .
eq rcvd-list receiver a = FL .
eq flag(sender a) = b .
eq flag(receiver a) = (not b) .

**
** 
-- eof

red sndng-list(sender  m(m(m(m(a))))) .
red rcvd-list(receiver m(m(m(m(a))))) .
red flag(sender        m(m(m(m(a))))) .
red flag(receiver      m(m(m(m(a))))) . 

red sndng-list(sender  m(m(m(m(m(m(m(m(a))))))))) .
red rcvd-list(receiver m(m(m(m(m(m(m(m(a))))))))) .
red flag(sender        m(m(m(m(m(m(m(m(a))))))))) .
red flag(receiver      m(m(m(m(m(m(m(m(a))))))))) . 

red sndng-list(sender  m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(a))))))))))))))))) .
red rcvd-list(receiver m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(a))))))))))))))))) .
red flag(sender        m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(a))))))))))))))))) .
red flag(receiver      m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(a))))))))))))))))) .

close

-- --------------41BEF9B28048CB33146F26EC--


