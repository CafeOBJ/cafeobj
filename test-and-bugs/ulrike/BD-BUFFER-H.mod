module BD-BUFFER-H { 
  import { 
    protecting (BD-BUFFER)
    protecting (MSG-ALGEBRA)
    protecting (SUBCONFIGURATION)
  }
 
  signature { 
    class Flag {
      buffer : ObjectId 
    }
    class FSet [Flag] { }
    class FUnset [Flag] { }

    [Flag BdBuffer < Subconfiguration] 
    class HBdBuffer {
      conf : Subconfiguration
    }
 
    op flag-set _            : ObjectId -> Message 
    op flag-unset _          : ObjectId -> Message 
    op flag-reset _          : ObjectId -> Message 
    op gget _ replyto _      : ObjectId ObjectId -> Message 
  }

  axioms {
     vars B U F S : ObjectId 
     var  C       : Subconfiguration
     var  E       : Elem 
     vars B-ATTS F-ATTS H-ATTS : Attributes

  rl [S]: (flag-set F)   < F : Flag | F-ATTS >  => < F : FSet   | F-ATTS > .
  rl [U]: (flag-unset F) < F : Flag | F-ATTS >  => < F : FUnset | F-ATTS > . 
  rl [R]: (flag-reset F) < F : FSet | F-ATTS >  => < F : FUnset | F-ATTS > . 


  eq [E1]: (gget B replyto U) 
           < B : HBdBuffer | (conf = < B : BdBuffer | B-ATTS > 
                                     < F : Flag | buffer = B, F-ATTS >  
                                     C), 
                             H-ATTS > 
            = < B : HBdBuffer | (conf = ((get B replyto U) | (flag-reset F))
                                         < B : BdBuffer | B-ATTS > 
                                         < F : Flag | buffer = B, F-ATTS > 
                                         C), 
                                H-ATTS > .

  eq [E2]: < B : HBdBuffer | (conf = (to U answer to get is E) C), H-ATTS >  
         = < B : HBdBuffer | (conf = C), H-ATTS > 
             (to U answer to get is E) .

  eq [E3]: (put E into B)
           < B : HBdBuffer | (conf = (< B : BdBuffer | B-ATTS > 
                                      < F : Flag | buffer = B, F-ATTS >) 
                                      C), 
                              H-ATTS  > 
        = < B : HBdBuffer | (conf = ((put E into B) | (flag-set F)) 
                                     < B : BdBuffer | B-ATTS >
                                     < F : Flag | buffer = B, F-ATTS > 
                                     C) , 
                             H-ATTS > . 
 
  eq [E4]: (get B replyto U)
           < B : HBdBuffer | (conf = < B : BdBuffer | B-ATTS > 
                                     < F : Flag | buffer = B, F-ATTS >
                                     C), 
                             H-ATTS >
         = < B : HBdBuffer | (conf = ((get B replyto U) | (flag-unset F)) 
                                      < B : BdBuffer | B-ATTS > 
                                      < F : Flag | buffer = B, F-ATTS > 
                                      C ),
                              H-ATTS > .
  }
}