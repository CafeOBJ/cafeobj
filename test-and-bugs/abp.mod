-- Date: Tue, 21 Apr 1998 21:20:57 +0000
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- Organization: University "A.I.Cuza",  Faculty of Computer Science
-- X-Mailer: Mozilla 4.04 [en] (X11; I; Linux 2.0.33 i586)
-- MIME-Version: 1.0
-- To: Toshimi Sawada <sawada@sra.co.jp>
-- Subject: "apply" sequence
-- Content-Transfer-Encoding: 7bit
-- Content-Type: text/plain; charset=us-ascii
-- Content-Length: 11917

-- Dear Toshimi,

-- Below is a specification of a "realiable" ABP (I'm working now to new
-- version of ABP which is almost finished) and two lemmas about it. I
-- think that the "apply" sequences in the two lemmas can be simplified
-- (unfortunately I'm not ablle to use efficiently this command). I will
-- appreciate any suggestion from your side. Thank you very much.
-- Best regards,
-- Dorel.
-- ***************************************************************

mod* MSG { [ Msg ] }

mod! MSG-BOOL {
  protecting (2TUPLE (C1 <= view to MSG {sort Elt -> Msg},
		      C2 <= view to BOOL {sort Elt -> Bool})
	      * {sort 2Tuple -> Msg-Bool})
}

mod! ACKN {
  [ Ackn ]
  ops send rec : -> Ackn
  op not_ : Ackn -> Ackn

  eq not rec = send .
  eq not send = rec .
}


mod* SENDER/RECEIVER (X :: MSG, Y :: MSG) {
  protecting (ACKN)

  *[ SenderReceiver ]*

  op init : -> SenderReceiver
  -- the only method: it could be a sending or a receiving
  op m : SenderReceiver -> SenderReceiver --  { coherent }
  -- the attribute flag: it represents the alternate bit
  bop flag : SenderReceiver -> Bool
  -- the attribute ackn: it tells the kind of action performed by the method
  bop ackn : SenderReceiver -> Ackn
  -- the sending message (attribute)
  bop msg-send_ : SenderReceiver -> Msg.X
  -- the receiving message (attribute)
  bop msg-rec_ : SenderReceiver -> Msg.Y { strategy (0 1) }

  var SR : SenderReceiver

  -- the first action is a sending
  eq ackn(init) = send .
  -- the sendings and receivings alternate
  eq ackn(m(SR)) = not ackn(SR) .
}

mod* SENDER-ABP {
  protecting (SENDER/RECEIVER(X <= view to MSG-BOOL {sort Msg -> Msg-Bool}
			      Y <= view to BOOL {sort Msg -> Bool}
			      )*{hsort SenderReceiver -> Sender
				 op init -> init-S })
  
  var S : Sender

  -- initially, the flag is set on true
  eq flag(init-S) = true .
  -- the cases when the flag is not changing
  ceq flag(m(S)) = flag(S)
    if (ackn(S) == send) or
      (ackn(S) == rec and
	 msg-rec m(S) == (not flag(S))) .
  -- the case when the flag is changing
  ceq flag(m(S)) = not flag(S)
    if (ackn(S) == rec and
	  msg-rec m(S) == flag(S)) .
  -- the cases when the second component of the sending message
  -- remains unchanged
  ceq msg-send m(S) =  msg-send S
    if (ackn(S) == rec) or
      (ackn(S) == send and
	 flag(m(S)) == flag(S)) .
  -- the second component of the sending message is always the flag
  -- the receiving message remains unchanged while is sending
  ceq msg-rec (m(S)) = msg-rec S
    if ackn(S) == send .
}

mod* RECEIVER-ABP {
  protecting (SENDER/RECEIVER(Y <= view to MSG-BOOL {sort Msg -> Msg-Bool},
			      X <= view to BOOL {sort Msg -> Bool}
			      )*{ hsort SenderReceiver -> Receiver
				  op init -> init-R })
  
  var R : Receiver

  -- initially, the flag is set on false
  eq flag(init-R) = false .
  -- the cases when the flag remains unchanged
  ceq flag(m(R)) = flag(R)
    if (ackn(R) == send) or
      (ackn(R) == rec and
	 2* msg-rec m(R) == flag(R)) .
  -- the case when the flag is changed
  ceq flag(m(R)) = not flag(R)
    if (ackn(R) == rec and
	  2* msg-rec m(R) == (not flag(R))) .
  -- the sending message is always the flag
  eq msg-send R = flag(R) .
  -- the receiving message remains unchanged while is sending
  ceq msg-rec m(R) = msg-rec R
    if ackn(R) == send .
}

mod* BUFFER(X :: MSG) {
  *[Buffer]*
  op init-B : -> Buffer
  op put : Buffer Msg -> Buffer { coherent }
  bop get : Buffer ->  Msg

  var B : Buffer
  var M : Msg

  eq get(put(B,M)) = M .
}

mod* CH1 {
  protecting (BUFFER (X <= view to MSG-BOOL {sort Msg -> Msg-Bool})
	      *{hsort Buffer -> Ch1,
		op init-B -> init-CH1 })
}

mod* CH2 {
  protecting (BUFFER (X <= view to BOOL {sort Msg -> Bool})
	      *{ hsort Buffer -> Ch2,
		 op init-B -> init-CH2 })
}


mod* RABP {
  protecting (SENDER-ABP + CH1 + RECEIVER-ABP + CH2)
  *[ Abp ]*

  op init : -> Abp
  -- there is just one method
  op m : Abp -> Abp { coherent }
  -- projections on the components
  bop ch1_ : Abp -> Ch1
  bop ch2_ : Abp -> Ch2
  bop sender_ : Abp -> Sender
  bop receiver_ : Abp -> Receiver

  var A : Abp

  -- initial state
  eq ch1 init = init-CH1 .
  eq ch2 init = init-CH2 .
  eq sender init = init-S .
  eq receiver init = init-R .

  -- synchronization equations
  eq sender m(A) = m(sender A) .
  eq receiver m(A) = m(receiver A) .
  -- -- the sender is  sending
  ceq [ch1-1] : ch1 m(A) = put(ch1 A, msg-send sender A)
    if (ackn(sender A) == send) .
  -- -- the sender is receiving
  ceq [mrs] : msg-rec sender m(A) = get(ch2 m(A))
  if (ackn(sender A) == rec) .
  ceq [ch1-2] : ch1 m(A) = ch1 A
    if ackn(sender A) == rec .
  -- -- the receiver is receiving
  ceq [mrr] : msg-rec receiver m(A) = get(ch1 m(A))
    if  ackn(receiver A) == rec .
  ceq [ch2-1] : ch2 m(A) = ch2 A
    if ackn(receiver A) == rec .
  -- -- the receiver is sending
  ceq [ch2-2] : ch2 m(A) = put(ch2 A, msg-send receiver A)
  if (ackn(receiver A) == send) .
  
  -- equations for confluence

  ceq msg-rec m(sender A) = get(ch2 m(A))
    if (ackn(sender A) == rec) .
  ceq msg-rec m(receiver A) = get(ch1 m(A))
    if  ackn(receiver A) == rec .
}

-- ------------------------------------------------
-- Lemma 1
--          If
--              ackn(sender A) = send and
--              msg-send(sender A) = << msg ; b >> and
--              ackn(receiver A) = send and
--              msg-send(receiver A) =  not b
--          Then
--              ackn(sender m(m(A))) = send and
--              msg-send(sender m(m(A))) = << msg ; b >> and
--              ackn(receiver m(m(A))) = send and
--              msg-rec(receiver m(m(A))) = << msg ; b >> and
--              msg-send(receiver A) =   b
-- ------------------------------------------------
--> lemma 1: step 1
mod  PROOF1-RABP {
  protecting(RABP)
  op a   : -> Abp
  op msg : -> Msg
  op b   : -> Bool

  eq ackn(sender a) = send .
  eq ackn(sender m(a)) = rec .
  eq msg-send(sender a) = << msg ; b >> .
  eq flag(sender a) = b .
  eq ackn(receiver a) = send .
  eq ackn(receiver m(a)) = rec .
  eq msg-send(receiver a) = (not b) .
  eq flag(receiver a) = (not b) .
}

open PROOF1-RABP

-->     red msg-rec(sender m(m(a))) == (not b) .
red msg-rec(sender m(m(a))) == (not b) .
-- start msg-rec(sender m(m(a))) .
-- apply .mrs at term .
-- apply reduce at term .
-- apply .ch2-1 within term .
-- apply reduce at term .
-- apply .ch2-2 within term .
-- apply reduce at term .
-- apply reduce at term .
-->     red msg-rec(receiver m(m(a))) == << msg ; b >> .
red msg-rec(receiver m(m(a))) == << msg ; b >> .
-- start msg-rec(receiver m(m(a))) .
-- apply .mrr at term .
-- apply reduce at term .
-- apply .ch1-2 within term .
-- apply reduce at term .
-- apply .ch1-1 within term .
-- apply reduce at term .
-- apply reduce at term .
** 
close


--> lemma 1: step 2

open PROOF1-RABP
eq msg-rec(m(m(sender a))) = not b .           -- step 1
eq msg-rec(m(m(receiver a))) = << msg ; b >> . -- step 1
eq not not B:Bool = B .  -- a lemma on booleans

red ackn(sender m(m(a))) == send .               -- it should be true
red msg-send(sender m(m(a))) == << msg ; b >> .  -- it should be true
red msg-rec(sender m(m(a))) == (not b) .         -- it should be true
red flag(sender m(m(a))) == b .                  -- it should be true
red ackn(receiver m(m(a))) == send .             -- it should be true
red msg-send(receiver m(m(a))) == b .            -- it should be true
red msg-rec(receiver m(m(a))) == << msg ; b >> . -- it should be true
red flag(receiver m(m(a))) == b .                -- it should be true
close

-- ------------------------------------------------
-- Lemma 2
--          If
--              ackn(sender A) = send and
--              msg-send(sender A) = << msg ; b >> and
--              ackn(receiver A) = send and
--              msg-send(receiver A) =  b and
--              msg-rec(receiver m(m(A))) = << msg ; b >>
--          Then
--              ackn(sender m(m(A))) = send and
--              2* msg-send(sender m(m(A))) = not b and
--              ackn(receiver m(m(A))) = send and
--              msg-rec(receiver m(m(A))) = << msg ; b >> and
--              msg-send(receiver A) =   b
-- ------------------------------------------------
--> lemma 2:  step 1
mod PROOF2-RABP {
  protecting(RABP)
  op a   : -> Abp
  op msg : -> Msg
  op b   : -> Bool

  eq ackn(sender a) = send .
  eq ackn(sender m(a)) = rec .
  eq msg-send(sender a) = << msg ; b >> .
  eq flag(sender a) = b .
  eq ackn(receiver a) = send .
  eq ackn(receiver m(a)) = rec .
  eq msg-send(receiver a) = b .
  eq flag(receiver a) = b .
}

open PROOF2-RABP
-->     red msg-rec(sender m(m(a))) == b .
red msg-rec(sender m(m(a))) == b .
-- start msg-rec(sender m(m(a))) .
-- apply .mrs at term .
-- apply reduce at term .
-- apply .ch2-1 within term .
-- apply reduce at term .
-- apply .ch2-2 within term .
-- apply reduce at term .
-- apply reduce at term .
-->     red msg-rec(receiver m(m(a))) == << msg ; b >> .
red msg-rec(receiver m(m(a))) == << msg ; b >> .
-- start msg-rec(receiver m(m(a))) .
-- apply .mrr at term .
-- apply reduce at term .
-- apply .ch1-2 within term .
-- apply reduce at term .
-- apply .ch1-1 within term .
-- apply reduce at term .
-- apply reduce at term .
close


--> lemma 2: step 2

open PROOF2-RABP
-- eq msg-rec(m(m(sender a))) = not b .           -- step 1
-- eq msg-rec(m(m(sender a))) = b .           -- step 1
eq msg-rec(sender m(m(a))) = b .           -- step 1
-- eq msg-rec(m(m(receiver a))) = << msg ; b >> . -- step 1
eq msg-rec(receiver m(m(a))) = << msg ; b >> . -- step 1
eq not not B:Bool = B .  -- a lemma on booleans

red ackn(sender m(m(a))) == send .               -- it should be true
red msg-send(sender m(m(a))) == << msg ; b >> .  -- it should be true
red msg-rec(sender m(m(a))) == (not b) .         -- it should be true
red flag(sender m(m(a))) == b .                  -- it should be true
red ackn(receiver m(m(a))) == send .             -- it should be true
red msg-send(receiver m(m(a))) == b .            -- it should be true
red msg-rec(receiver m(m(a))) == << msg ; b >> . -- it should be true
red flag(receiver m(m(a))) == b .                -- it should be true
-- close

** eof
eof

