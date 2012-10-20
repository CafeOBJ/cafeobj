module SRB { 
  import {
    protecting (BD-BUFFER)
  }

  signature {
    class Sender {
      sendq  : List
      buffer : ObjectId
    }
    
    class Receiver {
      incoming : List
      buffer   : ObjectId 
    }
  
    op new Sender with _ and _ replyto _ : List ObjectId ObjectId -> Message 
    op new Receiver with _ replyto _     : ObjectId ObjectId -> Message 
    op to _ the new Sender is _          : ObjectId ObjectId -> Message   
    op to _ the new Receiver is _        : ObjectId ObjectId -> Message 
    }

  axioms {
    vars  S R B U : ObjectId 
    vars  C L : List
    vars  I O : Nat
    var   E : Elem 
    var   ATTS : Attributes 

    rl [S1]: < S : Sender | sendq =  L E, buffer = B, ATTS >
             => < S : Sender | sendq = L, buffer = B, ATTS >
                (put E into B) . 
  
    rl [R1]: < R : Receiver | ATTS >
             => < R : Receiver | ATTS >
                (get B replyto R) .

    rl [R2]: (to U answer to get is E)
             < R : Receiver | incoming = L, buffer = B, ATTS >
             => < R : Receiver | incoming = E L, buffer = B, ATTS >
                (get B replyto R) .
 
    rl [NR]: (new Receiver with B replyto U) 
             < P : Proto | class = Receiver, next = R  >
             => < P : Proto | class = Receiver, next = incoid(R) >
                < R : Receiver | incoming = eps, buffer = B >
                (to U the new Receiver is R) .

    rl [NS]: (new Sender with L and B replyto U) 
             < P : Proto | class = Sender, next = S >
             => < P : Proto | next = incoid(S), next = S >
                < S : Sender | sendq = L, buffer = B >
                (to U the new Sender is S) .
 }
}