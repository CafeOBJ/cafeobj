
mod* GROUP {
  [ Elem ]
  op e : -> Elem
  op -_ : Elem -> Elem
  op _+_ : Elem Elem -> Elem
  vars X Y Z X* Y* Z* : Elem
  trans [1]: e + X => X .
  trans [2]: (- X) + X => e .
  trans [3]: (X + Y) + Z => X + (Y + Z) .
}
