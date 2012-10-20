require Msimple-nat
require Milist

module NAT-ILIST {
  protecting (ILIST(IDX <= view to SIMPLE-NAT { sort Elt -> Nat },
		    DAT <= view to SIMPLE-NAT { sort Elt -> Nat })
	      * { sort Ilist -> Ilist-of-Nat })
}

provide Mnat-ilist

eof

** $Id: Mnat-ilist.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
