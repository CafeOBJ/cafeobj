module BD-BUFFER-2 {
  import { 
    protecting (BD-BUFFER)
    protecting (MSG-ALGEBRA)
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
    var  ATTS : Attributes 

  eq [E1]: (get2 B replyto U)
           < B : BdBuffer2 | ATTS >  
           = < B : BdBuffer2 | ATTS  > 
             ((get B replyto U);;(get B replyto U)) .

  eq [E2]: ((to U answer to get is E);;(to U answer to get is F))
           = (to U answer to get2 is F and E) . 
  }
}