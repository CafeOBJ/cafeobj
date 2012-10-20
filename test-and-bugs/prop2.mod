set include BOOL off

mod! PROPC'
{
  signature {
    [ Prop, Bool Id < Prop ]
    ops true false : -> Bool
    op _ and _ : Prop Prop -> Prop { assoc comm constr prec: 55 }
    op _ xor _ : Prop Prop -> Prop { assoc comm constr prec: 57 }
    op _ or _ : Prop Prop -> Prop { assoc comm prec: 59 }
    op not _ : Prop -> Prop { strat: (0 1) prec: 53 }
    op _ -> _ : Prop Prop -> Prop { strat: (0 1 2) prec: 61 }
    op _ <-> _ : Prop Prop -> Prop { assoc prec: 63 }
  }
  axioms {
    vars p q r : Prop
    eq p and false = false .
    eq p and true = p .
    eq p and p = p .
    eq p xor false = p .
    eq p xor p = false .
    eq p and (q xor r) = p and q xor p and r .
    eq p or q = p and q xor p xor q .
    eq not p = p xor true .
    eq p -> q = p and q xor p xor true .
    eq p <-> q = p xor q xor true .
  }
}

-- open PROPC'
-- ops 'a 'b : -> Id .
-- reduce 'a or 'b <-> 'b or 'a .
-- set tram path brute
-- tram reduce 'a or 'b <-> 'b or 'a .
