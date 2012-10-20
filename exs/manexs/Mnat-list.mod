require Msimple-nat
require Milist

module NAT-ILIST {
  protecting (ILIST(IDX <= view to SIMPLE-NAT { sort Elt -> Nat },
		    DAT <= view to SIMPLE-NAT { sort Elt -> Nat }))
}

view V from ONE to SIMPLE-NAT {
  sort Elt -> Nat
}

module NAT-ILIST' {
  protecting (ILIST(IDX <= V, DAT <= V))
}

module NAT-ILIST'' {
  protecting (ILIST(SIMPLE-NAT { sort Elt -> Nat },
		    SIMPLE-NAT { sort Elt -> Nat }))
}

provide Mnat-list

eof

** $Id: Mnat-list.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
