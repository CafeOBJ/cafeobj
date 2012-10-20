mod A {
  [ S ]
  op _=_ : S S -> Bool
}

mod B {
  us (A)
  op b : -> S
}

mod C {
  us (A)
  op c : -> S
}

mod D {
  pr(B)
  pr(C)
}
