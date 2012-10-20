** -*- Mode:CafeOBJ -*-

module! TICKET {
  [ Place < Marking ]
  ops $ q t1 t2 : -> Place
  op null : -> Marking
  op __ : Marking Marking -> Marking {assoc comm id: null}
  trans [b-t1]: $ => t1 q q .
  trans [b-t2]: $ => t2 q .
  trans [change]: $ => q q q q .
  trans [b'-t1]: $ q q => t1 .
  trans [b'-t2]: $ q q q => t2 .
}

--
eof
--
$Id: ticket.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
