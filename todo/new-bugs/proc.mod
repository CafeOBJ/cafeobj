mod PROCS-RESOURCES {
  [ Resources Process < State ]
  ops res null : -> Resources { constr }
  op p : Resources -> Process { constr }
  op __ : Resources Resources -> Resources { constr assoc comm id: null }
  op __ : State State -> State { constr assoc comm id: null }

  trans [acq1]: p(null) res => p(res) .
  trans [acq2]: p(res) res => p(res res) .
  trans [rel] : p(res res) => p(null) res res .
  trans [dupl]: p(null) res => p(null) res p(null) res .
}

** eof
** 
red in PROCS-RESOURCES : res p(null) =(1)=>! X:State .

open PROCS-RESOURCES .
pred s= : State State .
eq (s=(S1:State, S2:State)) = true .

red p(null) =(1)=>! X:State suchThat s=(X1:State, X2:State) .

red p(null) =(1)=>! X:State suchThat s=(X1:State, X1:State) .
