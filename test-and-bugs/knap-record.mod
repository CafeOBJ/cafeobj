module TEST {
  signature {
    [ M ]

    op c : -> M
  }
}


module TESTPAR[P :: TEST] {
  signature {
    record Test {
      attr : M
    }
  }
}

module TESTINST {
  imports {
    protecting (TESTPAR[NAT { sort M -> Nat, op c -> p(s(0)) }])
  }
}

-- reduce makeTest .
