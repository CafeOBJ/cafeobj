module STORE {
  pr (ZZ)
  pr (Id * { sort Id -> Var })
  signature {
    [ Store ]
    op _[[_]] : Store Var -> Int
    op _;_:=_ : Store Var Var -> Store
  }
  axioms {
    vars X Y Z  : Var
    var S : Store
    eq S ; X := Y [[X]] = S [[Y]] .
    cq S ; X := Y [[Z]] = S [[Z]] if X =/= Z .
  }
}

 
