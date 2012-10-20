-- ============================================================
mod! BAG (X :: TRIV) { us(EQL)
  [Elt < Bag]
  op _in_  : Elt Bag -> Bool
  op _ _ : Bag Bag -> Bag {assoc comm}
  vars E1 E2 : Elt
  var S : Bag
  eq E1 in (E2) = (E1 = E2) .
  eq E1 in (E2 S) = if (E1 = E2) then true else (E1 in S) fi .
}

mod! SET (X :: TRIV) {
  us(BAG(X) * {sort Bag -> Set})
  eq (E:Elt E) = E .
}

mod! INT= { ex(INT) us(EQL)
  eq (N1:Nat = N2:Nat) = (N1 == N2) . }

open (SET(INT={sort Elt -> Int}))
red 3 = 4 .
red 3 3 3 3 4 4 5 .
red 4 in (3 3 3 3 4 4 5) .
red 2 in (3 3 3 3 4 4 5) .
close

-- this does not work
-- + EQL masks the equation:
--   eq (N1:Nat = N2:Nat) = (N1 == N2) . }
open (SET(INT={sort Elt -> Int}) + EQL)
red 3 = 4 .
red 3 3 3 3 4 4 5 .
red 4 in (3 3 3 3 4 4 5) .
red 2 in (3 3 3 3 4 4 5) .
close
