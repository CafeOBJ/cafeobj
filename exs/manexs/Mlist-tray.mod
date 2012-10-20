require Mtray
require Mlist

view LIST-AS-STACK from STACK to LIST {
  sort Stack -> NeList
  op push -> __
}

module LIST-TRAY {
  protecting (TRAY(Y <= LIST-AS-STACK))
}

provide Mlist-tray

eof

** $Id: Mlist-tray.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
