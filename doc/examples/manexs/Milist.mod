require Mone
module! ILIST ( IDX :: ONE, DAT :: ONE ) 
{
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

provide Milist

eof

** $Id: Milist.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
