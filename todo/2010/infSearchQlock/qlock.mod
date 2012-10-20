-- ==========================================================
--> file: qlock.mod
-- ==========================================================

--> LABEL
mod! LABEL {
  -- EQL is a meta module 
  -- for making _=_ predicate available
  inc(EQL) 

  [LabelConst < Label]
  ops rm wt cs : -> LabelConst {constr}
  vars Lc1 Lc2 : LabelConst
  eq (Lc1 = Lc2) = (Lc1 == Lc2) .
}

--> PID
mod* PID {
  inc(EQL) 
  [PidConst < Pid < PidErr]
  vars Pc1 Pc2 : PidConst
  eq (Pc1 = Pc2) = (Pc1 == Pc2) .
}

--> TRIV=
mod* TRIV= {
  inc(EQL) 
  [EltConst < Elt < EltErr]
}

--> QUEUE
mod* QUEUE (D :: TRIV=) {
  inc(EQL)
  -- EQL needs not be imported because
  -- it is already imported by (D :: TRIV=)

  -- sort Queue and its constructors
  [Queue < QueueErr]
  op empty :             -> Queue {constr}
  op _,_   : Queue Elt.D -> Queue {constr}

  -- equality over Queue
  -- the following eq is implied by EQL
  -- eq (empty = empty) = true .
  eq (Q1:Queue,E1:Elt = Q2:Queue,E2:Elt) = (Q1 = Q2) and (E1 = E2) .

  -- CafeOBJ variables
  var Q : Queue 
  vars X Y : Elt.D

-- put
  op put : EltErr.D QueueErr -> QueueErr
  op put : Elt.D Queue -> Queue
  eq put(X,empty) = empty,X .
  eq put(X,(Q,Y)) = put(X,Q),Y .

-- get
  op get : QueueErr -> QueueErr
  eq get((Q,X)) = Q .
  eq (get(empty) = Q:Queue) = false .

-- top
  op top : QueueErr -> EltErr.D
  eq top((Q,X)) = X .
  eq (top(empty) = E:Elt.D) = false .

-- empty?
  pred empty? : QueueErr 
  eq empty?(empty) = true .
  eq empty?((Q,X)) = false .

-- (_ in _)
  pred (_in_) : EltErr.D QueueErr 
  eq (X in empty) = false .
  eq (X in (Q,Y)) = ((X = Y) or (X in Q)) .
}

--> QLOCK
mod* QLOCK {
  inc(LABEL)
  inc(QUEUE(PID{sort Elt -> Pid,
                sort EltConst -> PidConst,
                sort EltErr -> PidErr}))

-- state space of QLOCK
  *[Sys]*

-- initial state of QLOCK
  op init : -> Sys {constr}
-- actions
  bop want : Sys Pid -> Sys {constr}
  bop try  : Sys Pid -> Sys {constr}
  bop exit : Sys Pid -> Sys {constr}
-- observations
  bop pc    : Sys Pid -> Label
  bop queue : Sys -> Queue

-- observations for initial state
  eq pc(init,I:Pid)  = rm .
  eq queue(init) = empty .

-- CafeOBJ variables
  var S : Sys
  vars I J : Pid
  
-- want
  -- effective condition for want
  op c-want : Sys Pid -> Bool
  eq c-want(S,I) = (pc(S,I) = rm) .
  --
  ceq pc(want(S,I),J)  
      = (if I = J then wt else pc(S,J) fi) if c-want(S,I) .
  ceq queue(want(S,I)) = put(I,queue(S))   if c-want(S,I) .
  ceq want(S,I)        = S                 if not c-want(S,I) .

-- try
  -- effective condition for try
  op c-try : Sys Pid -> Bool
  eq c-try(S,I) = (pc(S,I) = wt and top(queue(S)) = I) .
  --
  ceq pc(try(S,I),J)  
      = (if I = J then cs else pc(S,J) fi) if c-try(S,I) .
  eq  queue(try(S,I)) = queue(S) .
  ceq try(S,I)        = S                  if not c-try(S,I) .

-- exit
  -- effective condition for exit
  op c-exit : Sys Pid -> Bool
  eq c-exit(S,I) = (pc(S,I) = cs) .
  -- 
  ceq pc(exit(S,I),J)  
      = (if I = J then rm else pc(S,J) fi) if c-exit(S,I) .
  ceq queue(exit(S,I)) = get(queue(S))     if c-exit(S,I) .
  ceq exit(S,I)        = S                 if not c-exit(S,I) .
}
