module! TICKET2 {
  [ Place < Marking ]
  ops $ q t1 t2 : -> Place
  op null : -> Marking
  op __ : Marking Marking -> Marking {assoc comm idr: null}
  trans [b-t1]: $ => t1 q q .
  trans [b-t2]: $ => t2 q .
  trans [change]: $ => q q q q .
  trans [b'-t1]: $ q q => t1 .
  trans [b'-t2]: $ q q q => t2 .
}

module! TRIVIAL-TRANS {
  [ Elt ]
  ops a b c d e f g h : -> Elt
  trans a => b .
  trans b => c .
  trans c => a .
  trans c => d .
  trans c => f .
  trans d => e .
  trans d => f .
  trans d => b .
  trans d => a .
  trans e => b .
  trans e => g .
  trans f => g .
}
