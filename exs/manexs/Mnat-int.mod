module NAT-INT {
  [ Nat < Int ]
  op _+_ : Nat Nat -> Nat
  op _+_ : Int Int -> Int
}

view ID from NAT-INT to NAT-INT {
  sort Nat -> Nat
  sort Int -> Int
  op _+_ -> _+_
}

view U from NAT-INT to NAT-INT {
  sort Nat -> Nat,
  sort Int -> Nat,
  op _+_ -> _+_
}

view L from NAT-INT to NAT-INT {
  sort Nat -> Int,
  sort Int -> Int,
  op _+_ -> _+_
}

provide Mnat-int

** $Id: Mnat-int.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
