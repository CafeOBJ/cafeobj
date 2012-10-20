mod L [ X :: TRIV ] {
  [ Elt < List ]
  op nil : -> List { constr }
  op _ _ : List List -> List { assoc idr: nil }
}


make L2 (L((L(NAT)*{op __ -> (_,_)}){sort Elt -> List}))

