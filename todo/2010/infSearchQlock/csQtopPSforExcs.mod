-- ==========================================================
--> file: csQtopPS.mod
-- ==========================================================

--> proof score file for the lemma:
--> (pc(S:Sys,I:Pid) = cs) implies (top(queue(S)) = I)

in qlock.mod
   
mod CSqTop {
 pr(QLOCK)
 op csQtop : Sys Pid -> Bool 
 eq csQtop(S:Sys,I:Pid) = 
     (pc(S,I) = cs) implies (top(queue(S)) = I) .
}

--> induction base
--> init
open CSqTop
   op i : -> Pid .
-- |-  
   red csQtop(init,i) .
close
--> induction step
--> want(s,i),c-want(s,i),queue(s)=empty,
open CSqTop
-- arbitrary objects
   op s : -> Sys .
   ops i j : -> PidConst .
-- inductive hypothesis
   -- eq csQtop(s,I:Pid) = true .
-- condition
   -- eq c-want(s,i) = true .
   eq pc(s,i) = rm .
--
   eq queue(s) = empty .
-- |-
-- check if the predicate is true in the next state
-- for possible two cases
   red csQtop(s,i) implies csQtop(want(s,i),i) .
   red csQtop(s,j) implies csQtop(want(s,i),j) .
close
--> want(s,i),c-want(s,i),queue(s)=q,i,
open CSqTop
-- arbitrary objects
   op s : -> Sys .
   ops i j : -> PidConst .
-- inductive hypothesis
   -- eq csQtop(s,I:Pid) = true .
-- condition
   -- eq c-want(s,i) = true .
   eq pc(s,i) = rm .
--
   op q : -> Queue .
   eq queue(s) = q,i .
-- |-
-- check if the predicate is true in the next state
-- for possible two cases
   red csQtop(s,i) implies csQtop(want(s,i),i) .
   red csQtop(s,j) implies csQtop(want(s,i),j) .
close
--> want(s,i),c-want(s,i),queue(s)=q,j,
open CSqTop
-- ...
close
--> want(s,i),~c-want(s,i)
open CSqTop
-- arbitrary objects
   op s : -> Sys .
   ops i j : -> PidConst .
-- inductive hypothesis
   -- eq csQtop(s,I:Pid) = true .
-- condition
   eq c-want(s,i) = false .
-- |-
-- check if the predicate is true in the next state
-- for possible two cases
   red csQtop(s,i) implies csQtop(want(s,i),i) .
   red csQtop(s,j) implies csQtop(want(s,i),j) .
close
--> try(s,i),c-try(s,i)
open CSqTop
-- arbitrary objects
   op s : -> Sys .
   ops i j : -> PidConst .
-- inductive hypothesis
   -- eq csQtop(s,I:Pid) = true .
-- condition
   -- eq c-try(s,i) = true .
   -- ...
-- |-
-- check if the predicate is true in the next state
-- for possible two cases
-- ...
close
--> try(s,i),~c-try(s,i)
open CSqTop
-- arbitrary objects
   op s : -> Sys .
   ops i j : -> PidConst .
-- inductive hypothesis
   -- eq csQtop(s,I:Pid) = true .
-- condition
   eq c-try(s,i) = false .
-- |-
-- check if the predicate is true in the next state
   red csQtop(s,i) implies csQtop(try(s,i),i) .
   red csQtop(s,j) implies csQtop(try(s,i),j) .
close
--> exit(s,i),c-exit(s,i),queue(s)=empty
open CSqTop
-- ...
close
--> exit(s,i),c-exit(s,i),queue(s)=q,i
open CSqTop
-- ...
close
--> exit(s,i),c-exit(s,i),queue(s)=q,j
open CSqTop
-- ...
close
--> exit(s,i),~c-exit(s,i)
open CSqTop
-- ...
close
