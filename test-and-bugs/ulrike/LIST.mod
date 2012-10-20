module LIST {

  signature {
    [Elem]
    [List]

    op eps : -> List
    op _ _ : Elem List -> List  
    op _ _ : List Elem -> List
  }

  axioms {
    vars E E1 E2 : Elem
    var  L : List

    eq [Eq1]:  E2 eps = eps E2 .
    eq [Eq2]:  E1 (L E2)  = (E1 L) E2 .
  }
}