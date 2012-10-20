--
-- Foldr Function
--

mod! LIST(X :: TRIV) {
  [List]
  op nil : -> List
  op _|_ : Elt.X List -> List
}

-- formal parameter list
mod* FPL {
  [Elt List]
  op nil : -> List
  op _|_ : Elt List -> List
}

mod* FUN2(X :: TRIV,L :: FPL) {
  op f : Elt.L Elt.X -> Elt.X
}

mod! FOLDR(X :: TRIV,L :: FPL,F :: FUN2(X,L)) {
  op foldr : Elt.X List.L -> Elt.X
  var E : Elt.X
  var E' : Elt.L
  var L : List.L
  eq foldr(E,nil) = E .
  eq foldr(E,E' | L) = f.F(E',foldr(E,L)) .
}


mod! AP3 {
  pr(FUN2(X <= view to LIST {sort Elt -> List},
          L <= view to LIST {sort Elt -> Elt, sort List -> List}))
}

mod! EX3 {
  pr(FOLDR(X <= view to LIST {sort Elt -> List},
           L <= view to LIST {sort Elt -> Elt, sort List -> List},
           F <= view to AP3 {op f -> _|_}))
  op app : List List -> List
  eq app(L1:List,L2:List) = foldr(L2,L1) .
}

open EX3
  ops a b c d : -> Elt .
  red app(a | b | nil,c | d | nil) .
close

open EX3(NAT)
  red app(0 | 1 | nil,2 | 3 | nil) .
close

-- 
eof

**
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- the following does not work
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

mod! AP3 (A :: TRIV) {
  pr(FUN2(X <= view to LIST(A) {sort Elt -> List},
          L <= view to LIST(A) {sort Elt -> Elt, sort List -> List}))
}

mod! EX3 (A :: TRIV) {
  pr(FOLDR(X <= view to LIST(A) {sort Elt -> List},
           L <= view to LIST(A) {sort Elt -> Elt, sort List -> List},
           F <= view to AP3(A) {op f -> _|_}))
  op app : List List -> List
  eq app(L1:List,L2:List) = foldr(L2,L1) .
}

open EX3
  ops a b c d : -> Elt .
  red app(a | b | nil,c | d | nil) .
close

open EX3(NAT)
  red app(0 | 1 | nil,2 | 3 | nil) .
close
