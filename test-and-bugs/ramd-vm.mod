-- *******************RAND-VM.MOD**************
mod* RAND-VM {
  protecting (VM + RAND1 + RAND2)

  bops #av-tea #av-coffee : St -> Nat
  -- bop #in-coffee : -> Rand1
  -- bop #in-tea : -> Rand2
  bop #in-conffee : St -> Rand1
  bop #in-tea : St -> Rand2
  var S : St

  eq #in-coffee(init1) = init1 .
  ceq #in-coffee(m(S)) = next(#in-coffee(S)) if #av-coffee(S) == 0 .

  eq #in-tea(init2) = init2 .
  ceq #in-tea(m(S)) = next(#in-tea(S)) if #av-tea(S) == 0 .
  
  eq #av-coffee(init) = 0 .
  ceq #av-coffee(m(S)) =  #av-coffee(S) if out(m(S)) == tea .
  ceq #av-coffee(m(S)) =  p #av-coffee(S) if (out(m(S)) == coffee) and 
                                       (#av-coffee(S) > 0) .
  ceq #av-coffee(m(S)) =  val(#in-coffee(m(S))) if #av-coffee(S) == 0 .
  
  eq #av-tea(init) = 0 .
  ceq #av-tea(m(S)) =  #av-tea(S) if out(m(S)) == coffee .
  ceq #av-tea(m(S)) =  p #av-tea(S) if (out(m(S)) == tea) and 
                                       (#av-tea(S) > 0) .
  ceq #av-tea(m(S)) =  val(#in-tea(m(S))) if #av-tea(S) == 0 .
}
eof
