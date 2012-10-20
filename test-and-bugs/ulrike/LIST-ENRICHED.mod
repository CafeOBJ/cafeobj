module LIST-ENRICHED {
  import {
    protecting (NAT)
    protecting (LIST)
  }
  
  signature {
    op length : List -> Nat
    op first  : List -> Elem
    op removefirst : List -> List 
    op iselem : Elem List -> Bool
    op select : List -> Elem 
    op remove : Elem List -> List 
  }
  
  axioms {
    var  L    : List
    vars E E' : Elem
  
  eq [Eq3]: length(eps) = 0 .
  eq [Eq4]: length(E L) = 1 + length(L) .
  eq [Eq5]: length(L E) = 1 + length(L) .
   
  eq [Eq6]: first(E L) = E .
  eq [Eq7]: removefirst(E L) = L .
 
  eq [Eq8]: iselem(E, eps) = false .
  eq [Eq9]: iselem(E, L E) = true .
  eq [Eq10]: iselem(E, L E') = (E == E') .

  eq [Eq11]: select(L E) = E .
 
  eq  [Eq12]: remove(E, L E) = L .
  ceq [Eq13]: remove(E, L E') = remove(E, L) E' if E =/= E' .
  }
}