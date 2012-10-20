module EXT-ACZ-CONFIGURATION { 
  import {
    protecting (NAT)
    protecting (ACZ-CONFIGURATION) 
  }
  
  signature {
   op mkoid   : ClassId Nat -> ObjectId
   op incoid  : ObjectId -> ObjectId
  }

  axioms {   
    var  N : Nat
    var  A : ClassId

    eq [inc]: incoid(mkoid(A,N)) =  mkoid(A,s(N)) .
  }
} 