require Milist-ext

module NAT-ILIST-EXT {
  protecting (ILIST-EXT(IDX <= view to SIMPLE-NAT { sort Elt -> Nat },
			DAT <= view to SIMPLE-NAT { sort Elt -> Nat }))
}

provide Mnat-ilist-ext

eof

** $Id: Mnat-ilist-ext.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
