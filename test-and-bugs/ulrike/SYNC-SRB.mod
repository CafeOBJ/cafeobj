module SYNC-SRB { 
  import {
    protecting (NAT)
    protecting (LIST)
    protecting (EXT-ACZ-CONFIGURATION)
   }
  
  signature {
    class BdBuffer {
      in   : Nat 
      out  : Nat
      max  : NzNat
      cont : List 
    } 

    class Sender { 
      sendq  : List
      buffer : ObjectId 
    }

    class Receiver { 
      incoming : List
      buffer   : ObjectId 
    }

    op get _      : ObjectId -> Message 
    op put into _ : ObjectId -> Message 
   }

  axioms {
    vars S R B U : ObjectId
    var  E       : Elem
    vars C L     : List
    vars I O     : Nat
    var  M       : NzNat
    vars Buffer-ATTS Sender-ATTS Receiver-ATTS : Attributes 

  crl [P]: (put into B) 
           < S : Sender | sendq = L E, buffer = B, 
                          Sender-ATTS >
           < B : BdBuffer | cont = C, in = I, out = O, max = M, 
                            Buffer-ATTS > 
           => < B : BdBuffer | cont = E C, in = I + 1, out = O, max = M,
                               Buffer-ATTS >
              < S : Sender | sendq = L, buffer = B, 
                             Sender-ATTS >
           if sd(I,O) < M .

  rl [G]:  (get B) 
           < R : Receiver | incoming = L, buffer = B, 
                            Receiver-ATTS >
           < B : BdBuffer | cont = C E, in = I, out = O, max = M, 
                            Buffer-ATTS > 
           => < B : BdBuffer | cont = C, in = I, out = O + 1, max = M,
                               Buffer-ATTS >
              < R : Receiver | incoming = E L, buffer = B, 
                               Receiver-ATTS > .

  crl [PG]: (put into B)
            (get B) 
            < S : Sender | sendq = L E, buffer = B, 
                           Sender-ATTS >
            < R : Receiver | incoming = L, buffer = B, 
                             Receiver-ATTS  >
            < B : BdBuffer | cont = C, in = I, 
                             out = O, max = M, Buffer-ATTS > 
            => < B : BdBuffer | cont = E C, in = I + 1,
                                out = O + 1, max = M, Buffer-ATTS >
               < S : Sender | sendq = L, buffer = B, 
                              Sender-ATTS >  
               < R : Receiver | incoming = E L, buffer = B, 
                                Receiver-ATTS >
            if sd(I,O) < M . 
  }
}