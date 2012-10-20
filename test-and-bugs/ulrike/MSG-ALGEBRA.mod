module MSG-ALGEBRA { 
  import { 
    protecting (ACZ-CONFIGURATION)
    protecting (RWL)
  } 

  signature {
    op _ +  _  : Message Message -> Message 
    op _ ;  _  : Message Message -> Message 
    op _ ;; _  : Message Message -> Message 
    op _ |  _  : Message Message -> Message 
    op _ || _  : Message Message -> Message 
   }

  axioms {
    vars m n m1 m2 n1 n2   : Message  
    vars c d c1 c2 d1 d2 h : ACZ-Configuration

  crl [C]: (m + n) c => d
           if m c ==> d  or 
              n c ==> d .

  crl [S1]: (m1 ; m2) c => d
            if  m1 c   ==> h  and  
                m2 h   ==> d .

  crl [S2]: (m1 ;; m2) c => d (n1 ;; n2) 
            if m1 c  ==> n1 h and 
               m2 h  ==> n2 d .

  crl [P1]: (m1 | m2) c1 c2 => d1 d2
            if m1 c1 ==> d1 and 
               m2 c2 ==> d2 .

  crl [P2]: (m1 || m2) c1 c2 => d1 d2 (n1 || n2) 
            if m1 c1 ==> n1 d1 and
               m2 c2 ==> n2 d2 .
  }
}