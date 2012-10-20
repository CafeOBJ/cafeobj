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
  op m : SenderReceiver -> SenderReceiver { coherent }
-- the attribute flag: it represents the alternate bit
  bop flag : SenderReceiver -> Bool
-- the attribute ackn: it tells the kind of action performed by the method
  bop ackn : SenderReceiver -> Ackn
-- the sending message (attribute)
  bop msg-send_ : SenderReceiver -> Msg.X
-- the receiving message (attribute)
  bop msg-rec_ : SenderReceiver -> Msg.Y

  var SR : SenderReceiver

-- the first action is a sending
  eq ackn(init) = send .
-- the sendings and receivings alternate
  eq ackn(m(SR)) = not ackn(SR) .
}

mod* SENDER-ABP {
  protecting (SENDER/RECEIVER(X <= view to MSG-BOOL {sort Msg -> Msg-Bool}
			      Y <= view to BOOL {sort Msg -> Bool})
	      * {hsort SenderReceiver -> Sender
		 op init -> init-S
	       }
	      )

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
  ceq 1* msg-send m(S) = 1* msg-send S 
      if (ackn(S) == rec) or
         (ackn(S) == send and 
          flag(m(S)) == flag(S)) .
-- the second component of the sending message is always the flag
  eq 2* msg-send S = flag(S) .
-- the receiving message remains unchanged while is sending
  ceq msg-rec (m(S)) = msg-rec S
      if ackn(S) == send .
}

mod* RECEIVER-ABP {
  protecting (SENDER/RECEIVER(Y <= view to MSG-BOOL {sort Msg -> Msg-Bool},
			      X <= view to BOOL {sort Msg -> Bool})
	      *{hsort SenderReceiver -> Receiver
		op init -> init-R})

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

mod* UBUFFER (X :: TRIV) {
  *[ UBuffer ]*
  op init : -> UBuffer
-- the method which writes in the buffer
  op put : UBuffer Elt -> UBuffer  { coherent }
-- the method which reads from the buffer
  bop get : UBuffer -> Elt
-- an acknowledge attribute which tells whether the message was lost or not
  bop empty? : UBuffer -> Bool

  var B : UBuffer
  var E : Elt
 
-- the message is read only if it  wasn't lost (recall that the buffer has the 
-- capacity 1)
  ceq get(put(B,E)) = E  if not empty?(put(B,E)) . ** and empty?(B) .
-- initially, the buffer is empty
  eq empty?(init) = true .
}

mod* CH1 {
  protecting (UBUFFER (X <= view to MSG-BOOL {sort Elt -> Msg-Bool})
	      *{hsort UBuffer -> Ch1,
		op init -> init-CH1})
}

mod* CH2 {
  protecting (UBUFFER (X <= view to BOOL {sort Elt -> Bool})
	      *{hsort UBuffer -> Ch2,
		op init -> init-CH2})
}

mod* ABP {
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
  ceq ch1 m(A) = put(ch1 A, msg-send sender A) 
       if (ackn(sender A) == send) .
-- -- the sender is receiving
  ceq msg-rec m(sender A) = get(ch2 A)  
       if (ackn(sender A) == rec) and
          (not empty?(ch2 A)) .
  ceq msg-rec m(sender A) = msg-rec sender A  
       if ackn(sender A) == rec and
          empty?(ch2 A) .
  ceq flag(m(sender A)) = flag(sender A)
      if empty?(ch2 A) and ackn(sender A) == rec .
  ceq ch1 m(A) = ch1 A 
       if ackn(sender A) == rec and not empty?(ch1 A) .
  ceq empty?(ch1 m(A)) = true
       if ackn(sender A) == rec and empty?(ch1 A) .
-- -- the receiver is receiving
  ceq msg-rec m(receiver A) = get(ch1 A)  
      if not empty?(ch1 A) and
         ackn(receiver A) == rec .
  ceq msg-rec m(receiver A) = msg-rec receiver A  
      if empty?(ch1 A) and
         ackn(receiver A) == rec .
  ceq flag(m(receiver A)) = flag(receiver A)
      if empty?(ch1 A) and ackn(receiver A) == rec .
  ceq ch2 m(A) = ch2 A 
       if ackn(receiver A) == rec and not empty?(ch2 A) .  
  ceq empty?(ch2 m(A)) = true 
       if ackn(receiver A) == rec and
          empty?(ch2 A) . 
-- -- the receiver is sending
  ceq ch2 m(A) = put(ch2 A, msg-send receiver A) 
       if (ackn(receiver A) == send) .
}

eof
