module BD-BUFFER-X {
  import { 
    protecting (BD-BUFFER)
  }

  signature {
    class XBdBuffer [BdBuffer] {
    }
  
  op last _ replyto _         : ObjectId ObjectId  -> Message 
  op to _ answer to last is _ : ObjectId Elem -> Message 
  }

  axioms {
    vars B U  : ObjectId 
    var  E    : Elem 
    var  C    : List 
    vars I O  : Nat 
    vars ATTS : Attributes 

  rl [L]: (last B replyto U) 
          < B : XBdBuffer | cont = E C, out = O, ATTS > 
          => < B : XBdBuffer | cont = C, out = O + 1, ATTS >
             (to U answer to last is E) .
  }
}