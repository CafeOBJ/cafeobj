-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- qlock protocol spec with transitions
-- and a complete proof score for mutual exclusion property
-- by using "red .. =(*,*)=> .. with ..(= (_ob=_))" command
-- by CafeOBJ team 071111

-- labels for process statuses
mod! LABEL {
  [Label]
  ops rm wt cs : -> Label
  -- rm: remaining,  wt: waiting, cs: critical section

  op _o=_ : Label Label -> Bool {comm}
  var L : Label
  eq (L o= L) = true .
  eq (rm o= wt) = false .
  eq (rm o= cs) = false .
  eq (wt o= cs) = false .
}

-- process identifiers
mod* PID {
  [Pid < PidErr]
  op none : -> PidErr  -- error process id
  op _o=_ : PidErr PidErr -> Bool {comm}
  var I : Pid
  eq (I o= I) = true .
  eq (I o= none) = false .
--  eq (none o= none) = true .
  eq (none o= none) = false .
}

mod* TRIVerr= { [Elt]
  [ Elt < EltErr ]
  op none : -> EltErr .
  pred _o=_ : EltErr EltErr .
  eq (E:Elt o= E) = true .
  eq (E:Elt o= none) = false .
}

mod! QUEUE(D :: TRIVerr=) {
  [Queue < QueueErr]
  op getEmpty : -> QueueErr
-- constructors
  op empty :             -> Queue {constr}
  op _,_   : Elt.D Queue -> Queue {constr}
-- operators
  op put : Queue Elt.D -> Queue
  op get : Queue -> Queue
  op top : Queue -> Elt.D
  pred empty? : Queue .
  pred _o=_ : QueueErr QueueErr .
-- CafeOBJ variables
  vars Q Q1 Q2 : Queue
  vars X Y : Elt.D
-- equations
  eq put(empty,X) = X,empty .
  eq put((Y,Q),X) = Y,put(Q,X) .
  eq get(empty) = getEmpty .
  eq get((X,Q)) = Q .
  eq top(empty) = none .
  eq top((X,Q)) = X .
  eq empty?(empty) = true .
  eq empty?((X,Q)) = false .
  eq (Q o= Q) = true .
  eq (Q o= getEmpty) = false .
  eq ((X,Q1) o= (Y,Q2)) = (X o= Y) and (Q1 o= Q2) .
}

view TRIVerr2PID from TRIVerr= to PID {
  sort EltErr -> PidErr
  sort Elt -> Pid
  op none -> none
}

mod* QLOCK {
  pr(LABEL)
  pr(QUEUE(D <= TRIVerr2PID))
  *[Sys]*
  pred _o=_ : Sys Sys .
  eq (S:Sys o= S) = true .
-- any initial state
  op init : -> Sys
-- observations
  bop pc    : Sys Pid -> Label {memo}
  bop queue : Sys -> Queue {memo}
-- actions
  bop want : Sys Pid -> Sys
  bop try  : Sys Pid -> Sys
  bop exit : Sys Pid -> Sys
-- CafeOBJ variables
  var S : Sys
  vars I J : Pid
-- for any initial state
  eq pc(init,I)  = rm .
  eq queue(init) = empty .
-- for want
  op c-want : Sys Pid -> Bool {strat: (0 1 2) memo}
  eq c-want(S,I) = (pc(S,I) o= rm) .
  --
  ceq pc(want(S,I),J)  = (if I o= J then wt else pc(S,J) fi) if
c-want(S,I) .
  ceq queue(want(S,I)) = put(queue(S),I)                     if
c-want(S,I) .
  ceq want(S,I)        = S                                   if not
c-want(S,I) .
-- for try
  op c-try : Sys Pid -> Bool {strat: (0 1 2) memo}
  eq c-try(S,I) = (pc(S,I) o= wt and top(queue(S)) o= I) .
  --
  ceq pc(try(S,I),J)  = (if I o= J then cs else pc(S,J) fi) if c-try(S,I) .
  eq  queue(try(S,I)) = queue(S) .
  ceq try(S,I)        = S                                   if not
c-try(S,I) .
-- for exit
  op c-exit : Sys Pid -> Bool {strat: (0 1 2) memo}
  eq c-exit(S,I) = (pc(S,I) o= cs) .
  --
  ceq pc(exit(S,I),J)  = (if I o= J then rm else pc(S,J) fi) if
c-exit(S,I) .
  ceq queue(exit(S,I)) = get(queue(S))                       if
c-exit(S,I) .
  ceq exit(S,I)        = S                                   if not
c-exit(S,I) .
}

mod! LIST (X :: TRIV) {
 [Elt < List]
 op (_ _) : Elt List -> List {constr} .
}

mod! PIDlist {pr((LIST(PID{sort Elt -> Pid}))*{sort List -> PidList})}

mod QLOCKsysEq {
 pr(QLOCK + PIDlist)

-- definition of (S:Sys =ob= Sys)
  pred (_=ob=_with_) : Sys Sys PidList {memo} .
  pred (_=pc_with_) : Sys Sys PidList .

  vars S S1 S2 : Sys .
  var P : Pid .
  var PL : PidList .

  eq (S1 =pc S2 with P) = (pc(S1,P) o= pc(S2,P)) .
  eq (S1 =pc S2 with (P PL)) = (pc(S1,P) o= pc(S2,P))
                                and (S1 =pc S2 with PL) .
  eq (S1 =ob= S2 with PL) = (S1 =pc S2 with PL)
                             and (queue(S1) o= queue(S2)) .
}

-- mutual exclusion property
mod MEX {
 pr(QLOCK)
 pred mutualEx : Sys Pid Pid .
 var S :  Sys . vars I J : Pid .
 eq mutualEx(S,I,J) = ((pc(S,I) o= cs and pc(S,J) o= cs) implies I o= J) .
}

-- for writing proof score for proving mutualEx property
mod! QLOCKijx {
  pr(QLOCK)

  ops i j : -> Pid .
  op x : -> Pid .  -- represent any Pid other than i j
  eq (i o= j) = false .
  eq (i o= x) = false .
  eq (j o= x) = false .

  [ Config ]
  op <_> : Sys -> Config .
  var S : Sys .
  -- possible transitions in transition rules
  trans [want-i] : < S > => < want(S,i) > .
  trans [want-j] : < S > => < want(S,j) > .
  trans [want-x] : < S > => < want(S,x) > .

  trans [try-i] : < S > => < try(S,i) > .
  trans [try-j] : < S > => < try(S,j) > .
  trans [try-x] : < S > => < try(S,x) > .

  trans [exit-i] : < S > => < exit(S,i) > .
  trans [exit-j] : < S > => < exit(S,j) > .
  trans [exit-x] : < S > => < exit(S,x) > .
 }

** eof

open (QLOCKsysEq + QLOCKijx + MEX)
pred mutualEx-ij : Sys .
var S : Sys .
eq mutualEx-ij(S) = mutualEx(S,i,j) .

pred _=ob=_ : Config Config {memo} .
vars S1 S2 : Sys .
eq (< S1 > =ob= < S2 >) = (S1 =ob= S2 with (i j x)) .

-- the following 9 reductions are working
red < init > =(10,4)=>* < S:Sys > .
red < init > =(100,2)=>* < S:Sys > .
red < init > =(100,4)=>* < S:Sys > .

red < init > =(1,4)=>* < S:Sys > suchThat (not mutualEx-ij(S)) .
red < init > =(1,5)=>* < S:Sys > suchThat (not mutualEx-ij(S)) .
red < init > =(1,8)=>* < S:Sys > suchThat (not mutualEx-ij(S)) .

red < init > =(100,4)=>* < S:Sys > withStateEq (C1:Config =ob= C2:Config) .
red < init > =(100,*)=>* < S:Sys > withStateEq (C1:Config =ob= C2:Config) .
red < init > =(*,*)=>* < S:Sys > withStateEq (C1:Config =ob= C2:Config) .

-- the following 2 reductions are not working
red < init > =(1,10)=>* < S:Sys >
       suchThat (not mutualEx-ij(S))
       withStateEq(C1:Config =ob= C2:Config) .

red < init > =(*,*)=>* < S:Sys >
       suchThat (not mutualEx-ij(S))
       withStateEq (C1:Config =ob= C2:Config) .
close

