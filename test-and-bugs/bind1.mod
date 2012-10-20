module TEST1 ( X :: TRIV * { sort Elt -> Men },
	       Y :: TRIV * { sort Elt -> Women }) {
  [ Men Women < Bonkers ]
  op fuck : Men Women -> Men { commutative }
  op fuck : Men Men -> Women
  op fuck : Women Women -> Women
  vars M M' : Men
  vars W W' : Women
  eq fuck(fuck(M,M'),fuck(W,W')) = fuck(M,W) .
}

module TEST2 {
  protecting (TEST1)
}

module TEST3 {
  protecting (TEST1 [ X <= view to NAT { sort Men -> Nat } ])
}

module TEST4 {
  protecting (TEST1 [ X <= view to NAT { sort Men -> Nat },
                      Y <= view to NAT { sort Women -> Nat } ])
}

