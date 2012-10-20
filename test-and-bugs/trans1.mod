module TEST {
  imports {
    protecting (RWL)
    protecting (NAT)
  }

  signature {
    [ T ]

    ops a b c d : -> T
  }

  axioms {
    trans a => b .
    trans b => c .
    ctrans c => d if a ==> b .
  }
}

-- reduce a ==> d .
