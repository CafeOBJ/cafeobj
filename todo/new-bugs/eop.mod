**> D
mod D { [ D ] }
**> L
mod L(X :: TRIV) { [ Elt < Lst ]}
**> M1
mod M1 {
  pr (L(D) * {sort D -> Elm})
}

**> D1
mod D1 { [ D ] op d : -> D }

**> D2
mod D2 { [D] op d : -> ?D }

**> M2
mod M2 {
  pr(L(D2))
}

**> M2'
mod M2' {
  pr(D2 * { sort D -> E })
  [ E < L ]
}

**> M3
mod M3 {pr(L(D2) * { sort D -> Elm })}

**> M3'
mod M3' {
  pr(M2 * { sort D -> Elm })
}

**> M4
mod M4 {
  pr(L(D2) * { sort Lst -> xLst })
}

**> M5
mod M5 {
  pr(L(D2{sort Elt -> D}) * { sort Lst -> xLst })
}

**> M6
mod M6 {
  pr(L(D1{sort Elt -> D}) * { sort Lst -> xLst })
}

**> M7
mod M7 {
  pr(D2)
  [ D < Lst ]
}


