module ILIST-EXT {
  protecting (ILIST)
  protecting (SIMPLE-NAT)
  op #_ : Ilist -> Nat
  var I : Elt.IDX.ILIST
  var D : Elt.DAT.ILIST
  var L : Ilist
  eq # put(I,D,L) = succ(0) + (# L) .
  eq # empty = 0 .
}
