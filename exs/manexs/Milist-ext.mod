require Milist
require Msimple-nat

module ILIST-EXT {
  protecting (ILIST)
  protecting (SIMPLE-NAT)
  op #_ : Ilist -> Nat
  var I : Elt.IDX
  var D : Elt.DAT
  var L : Ilist
  eq # put(I,D,L) = s(0) + (# L) .
  eq # empty = 0 .
}

provide Milist-ext

eof
--
** $Id: Milist-ext.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
