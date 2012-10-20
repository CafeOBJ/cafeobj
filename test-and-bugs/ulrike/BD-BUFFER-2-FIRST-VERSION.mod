module BD-BUFFER-TWO-FIRST-VERSION {
  import { 
    extending (BD-BUFFER)
  }
  
  signature {
    class BdBuffer2 [BdBuffer] {
    }
   
    op get2 _ replyto _               : ObjectId ObjectId  -> Message 
    op to _ answer to get2 is _ and _ : ObjectId Elem Elem -> Message 
  }

  axioms {
    vars B U  : ObjectId 
    vars E F  : Elem 
    var  C    : List 
    vars I O  : Nat 
    var  M    : NzNat  
    var  ATTS : Attributes

  rl [get]: (get2 B replyto U) 
             < B : BdBuffer2 | cont = C F E, out = O, ATTS > 
             => < B : BdBuffer2 | cont = C, out = O + 2, ATTS >
                (to U answer to get2 is F and E) . 
  }
}