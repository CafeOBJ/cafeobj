      
-- A ----X----> B

-- A ----X----> D


mod* A {
  [ a ]
}

mod* B (X :: A) {
  [ b ]
  op h : b -> a
  }

mod* D (X :: A,Y :: B(X)) {
}
       
mod* E (X :: A, Y :: B(X)) {
  protecting (D(X,Y))
}
