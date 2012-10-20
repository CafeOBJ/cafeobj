module* ONE {
  [ Elt ]
}

module! ILIST ( IDX :: ONE, DAT :: ONE ) {
  [ Ilist ]
  [ Elt.DAT < ErrD ]
  op undef : -> ErrD
  op empty : -> Ilist
  op put : Elt.IDX Elt.DAT Ilist -> Ilist
  op _[_] : Ilist Elt.IDX -> ErrD
  -- -----------------------------
  vars I I' : Elt.IDX
  var D : Elt.DAT
  var L : Ilist
  eq put(I,D,L) [ I' ] = if I == I' then D else L [ I' ] fi .
  eq empty [ I ] = undef .
}



