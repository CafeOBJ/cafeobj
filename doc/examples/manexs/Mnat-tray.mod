require Msimple-nat
require Mtray

module NAT-TRAY {
  protecting (TRAY(X.Y <= view to SIMPLE-NAT { sort Elt -> Nat }))
}

provide Mnat-tray

eof

** $Id: Mnat-tray.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
