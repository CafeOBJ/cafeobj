module BD-BUFFER { 
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

    class Proto {
      class : ClassId
      next  : ObjectId
    }
 
     op new BdBuffer with _ replyto _  : NzNat ObjectId -> Message
     op to _ the new BdBuffer is _     : ObjectId ObjectId -> Message 
     op get _ replyto _                : ObjectId ObjectId -> Message 
     op to _ answer to get is _        : ObjectId Elem -> Message 
     op put _ into _                   : Elem ObjectId  -> Message
   }

  axioms {
    vars B R U P : ObjectId
    var  E       : Elem
    var  C       : List
    vars I O     : Nat
    var  M       : NzNat  
    var  ATTS    : Attributes 

  crl [P]: (put E into B) 
           < B : BdBuffer | cont = C, in = I, max = M, ATTS >  
           =>  < B : BdBuffer | cont = E C, in = I + 1, max = M, ATTS >
           if sd(I,O) < M .


    rl [G]: (get B replyto R)
            < B : BdBuffer | cont = C E, out = O, max = M, ATTS > 
            => < B : BdBuffer | cont = C, out = O + 1, max = M, ATTS >
               (to R answer to get is E) .


    rl [N]: (new BdBuffer with M replyto U)
            < P : Proto | class = BdBuffer, next = B >
            => < P : Proto | class = BdBuffer, next = incoid(B) >
               < B : BdBuffer | cont = eps, in = 0, out = 0, max = M >
               (to U the new BdBuffer is B) .
 }
}
