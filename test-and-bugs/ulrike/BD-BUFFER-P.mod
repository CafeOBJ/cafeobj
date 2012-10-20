module BD-BUFFER-P {
  import { 
    protecting (BD-BUFFER-X) 
    protecting (BD-BUFFER-2)
    protecting (BD-BUFFER-H)
  } 
  
  signature {
    class PBufferI [BdBuffer2] {
    }
    [PBufferI < XBdBuffer]

    class PBuffer [HBdBuffer] {
    }
    
   op (_,_)                        : ObjectId ObjectId -> ObjectId

   op new PBuffer with _ replyto _ : NzNat ObjectId    -> Message 
   op to _ the new PBuffer is _    : ObjectId ObjectId -> Message
   }

  axioms {
    vars B U P F : ObjectId  
    vars E E'    : Elem  
    var  M       : NzNat
    var  C       : Subconfiguration 
    vars ATTS B-ATTS F-ATTS : Attributes
 

  eq [E1]: (last B replyto U)
           < B : PBuffer | (conf = C), ATTS > 
         = < B : PBuffer | 
                 (conf = C ((last B replyto U) | (flag-unset B))), ATTS > .

  eq [E2]: < B : PBuffer | (conf = C (to U answer to last is E)), ATTS >
           = < B : PBuffer | (conf = C), ATTS >
            (to U answer to last is E) .

  eq [E3]: (get2 B replyto U)
           < B : PBuffer | (conf = C), ATTS > 
         = < B : PBuffer | 
                 (conf = C ((get2 B replyto U) | (flag-unset B))), ATTS > .

  eq [E4]: < B : PBuffer | (conf = C (to U answer to get2 is E' and E)), ATTS >
           = < B : PBuffer | (conf = C), ATTS > 
             (to U answer to get2 is E' and E) .

  rl [N]: (new PBuffer with M replyto U)
          < P : Proto | class = PBuffer, next = (B,F) > 
          => < P : Proto | class = PBuffer, next = (incoid(B), incoid(F)) >
             < B : PBuffer | (conf = (< B : PBufferI | cont = eps, in = 0, 
                                                       out = 0, max = M >
                                      < F : FUnset | buffer = B >)) >  
             (to U the new PBuffer is B) .
  }
}
