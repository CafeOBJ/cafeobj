set mel sort on
set mel always on

mod* POSET {
  [ Elt ]

  pred _<=_ : Elt Elt
  pred _<_  : Elt Elt   

  vars E1 E2 E3 : Elt

  eq E1 <= E1 = true .
  cq E1 = E2      if (E1 <= E2) and (E2 <= E1) .
  cq (E1 <= E3) = true      if (E1 <= E2) and (E2 <= E3) .
  eq E1 < E2 = (E1 <= E2) and (E1 =/= E2) .
}

mod! ORDLIST (X :: POSET) {
  [ OrdList < List ]

  op nil : -> List 
  op _::_ : Elt List -> List 
-- some destructors like hd and tl if you wish
  var L : List
  vars A B : Elt   

  eq nil :is OrdList = true .
  eq A :: nil :is OrdList = true .
  ceq A :: (B :: L) :is OrdList = true if (A < B) and ((B :: L) :is OrdList) .
}

select ORDLIST(NAT) .

--> this should be (1 :: 2 :: nil) : OrdList
parse 1 :: 2 :: nil .
--> this should be (2 :: 1 :: nil) : List
parse 2 :: 1 :: nil .
