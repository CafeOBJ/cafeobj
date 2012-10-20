module BD-BUFFER-WITH-STATES { 
  import { 
    protecting (LIST-ENRICHED)
    protecting (EXT-ACZ-CONFIGURATION)
  } 
  
  signature {
    class BdBuffer {}

    class EmptyBdBuffer [BdBuffer] { 
      max : NzNat 
    }
 
    class FullBdBuffer [BdBuffer] {
      cont : List 
    } 
   
    class NormalBdBuffer [BdBuffer] {
      cont : List
      max  : NzNat 
    }
   
    class Proto {
      class : ClassId
      next  : ObjectId
    }
    
     op new BdBuffer with _ replyto _ : NzNat ObjectId -> Message 
     op to _ the new BdBuffer is _    : ObjectId ObjectId -> Message 
     op get _ replyto _               : ObjectId ObjectId -> Message 
     op to _ answer to get is _       : ObjectId Elem -> Message 
     op put _ into _                  : Elem ObjectId -> Message 
   }

  axioms {
    vars B U  : ObjectId   
    var  C    : List  
    var  E    : Elem  
    var  M    : NzNat
    var  ATTS : Attributes

  rl [P1] : (put E into B) 
            < B : EmptyBdBuffer | max = M, ATTS > 
            => < B : NormalBdBuffer | cont = E eps, max = M, ATTS > .

  crl [P2]: (put E into B) 
            < B : NormalBdBuffer | cont = C, max = M, ATTS > 
            => < B : NormalBdBuffer | cont = E C, max = M, ATTS >  
            if length(C) + 1 < M .

  crl [P3]: (put E into B) 
            < B : NormalBdBuffer | cont = C, max = M, ATTS > 
            => < B : FullBdBuffer | cont = E C, ATTS >  
            if (length(C) + 1 == M) .

  rl [G1]:  (get B replyto U) 
            < B : FullBdBuffer | cont = C E, ATTS > 
            => < B : NormalBdBuffer | cont = C, max = length(C) + 1, ATTS >
               (to U answer to get is E) .  

  rl [G2]:  (get B replyto U) 
            < B : NormalBdBuffer | cont = C E, ATTS > 
            => < B : NormalBdBuffer | cont = C, ATTS >
               (to U answer to get is E) .  

  rl [G3]:  (get B replyto U) 
            < B : NormalBdBuffer | cont = eps E, max = M, ATTS > 
            => < B : EmptyBdBuffer | max = M, ATTS >
               (to U answer to get is E) .  

  crl [N]:  (new BdBuffer with M replyto U) 
            < P : Proto | class = BdBuffer, next = B >
            => < P : Proto | class = BdBuffer, next = incoid(B) >
               < B : EmptyBdBuffer | max = M >
               (to U the new BdBuffer is B) 
               if  M > 1 .
  }
}