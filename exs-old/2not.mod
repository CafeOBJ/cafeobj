** -*- Mode:CafeOBJ -*-
-- from OBJ example 2not.obj
-- 
module! TIME {
  [ Time ]
  op 0 : -> Time 
  op s_ : Time -> Time 
}

module* WIRE {
  protecting (TIME + PROPC)
  op f1 : Time -> Prop 
}

module! NOT(W :: WIRE) {
  op f2 : Time -> Prop 
  var T : Time 
  eq f2(0) = false .
  eq f2(s T) = not f1(T) .
}

module! F {
  extending (TIME + PROPC)
  op t : -> Time 
  op f0 : Time -> Prop 
}

make 2NOT (NOT((NOT(F{op f1 -> f0})*{ op f2 -> f1 }){op f1 -> f0}))
select 2NOT
reduce f2(s s t) <-> f0(t) .
--
eof
--
$Id: 2not.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
