mod* MSG { [ Msg ] }

mod! ACKN {
  [ Ackn ]
  ops send rec : -> Ackn
  op not_ : Ackn -> Ackn
  
  eq not rec = send .
  eq not send = rec .
}


mod* SENDER/RECEIVER (X :: MSG) {


  *[ SenderReceiver ]*

  op init : -> SenderReceiver
  op m : SenderReceiver -> SenderReceiver { coherent }
  bop msg _ : SenderReceiver -> Msg
}

mod* SENDER (X :: MSG) {
  protecting(SENDER/RECEIVER(X) * {hsort SenderReceiver -> Sender
                                   op init -> init-S ,
                                   bop msg _ -> msg-send _
                                  })
}
 
mod* RECEIVER (X :: MSG) {
  protecting(SENDER/RECEIVER(X) * {hsort SenderReceiver -> Receiver
                                   op init -> init-R ,
                                   bop msg _ -> msg-rec _
                                  })
}
 


mod* SRP (X :: MSG) {
  protecting(ACKN)
  protecting (SENDER(X))
  protecting(RECEIVER(X))

  *[ St ]*
  op init : -> St
  op m : St -> St { coherent }
  bop ackn : St -> Ackn
  bop sender_ : St -> Sender
  bop receiver_ : St -> Receiver
  bop msg-send : St -> Msg
  bop msg-rec  : St -> Msg
 
  var S : St

  eq ackn(init) = send .
  eq ackn(m(S)) = not ackn(S) .

  eq sender init = init-S .
  eq receiver init = init-R .
  
  ceq msg-send(S) = msg-send(sender S) if ackn(S) == send .
  ceq msg-send(m(S)) = msg-send(S) if ackn(m(S)) == rec .
  ceq msg-rec(S) = msg-rec(receiver S) if ackn(S) == rec .
  ceq msg-rec(m(S)) = msg-rec(S) if ackn(m(S)) == send .

  eq msg-rec(m(S)) = msg-send(S) .
}

eof
