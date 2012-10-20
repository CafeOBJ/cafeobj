-- ==========================================================
--> file: simOfQLOCKbyQLOCKijPS.mod	
-- ==========================================================

in qlock.mod

set always memo on
clean memo

"{start of comments

let 
  (ops i j : -> PidConst .)
and let Sys(i,j) be a subsort of Sys which are composed of
terms of sort Sys which contain only i and j.

for any two distinct process identifiers i and j, and
for any reachable state s:Sys of QLOCK,
there exists a reachable state t:Sys(i,j) of QLOCK such that
   ( (pc(s,i) = pc(t,i)) and (pc(s,j) = pc(t,j)) ) and
     (pij(queue(s)) = queue(t))
     where pij(nil) = nil
           pij(Q:Queue,I:Pid) = pij(Q),I if (I=i or I=j)
                              = pij(Q)   if not(I=i or I=j)   
   
end of comments}"

mod QLOCKpij {
 pr(QLOCK)
 ops i j : -> PidConst
 op pij : Queue -> Queue .
--
 eq pij(empty) = empty .
 ceq pij(Q:Queue,I:Pid) = (pij(Q),I) 
                          if ((I = i) or (I = j)) .
 ceq pij(Q:Queue,I:Pid) = pij(Q)   
                          if not((I = i) or (I = j)) . 
 -- the following two conditional equations can be proved
 ceq pij(put(I:Pid,Q:Queue)) = put(I,pij(Q))
                          if ((I = i) or (I = j)) .
 ceq pij(put(I:Pid,Q:Queue)) = pij(Q)
                          if not((I = i) or (I = j)) .
}

-- verification by induction 
-- on the depth of the term structure of S:Sys

-- induction base:  s = init 
-- let t be init, for init is an element of Sys(i,j)
--> init
open QLOCKpij
ops i j : -> PidConst .
ops s t : -> Sys .
eq s = init .
eq t = init .
-- |- 
red (pc(s,i) = pc(t,i)) and (pc(s,j) = pc(t,j)) 
     and (pij(queue(s)) = queue(t)) .
close

-- induction step: 
-- let s be any term of sort Sys with depth n, and 
-- let assume that there exist a term t of sort Sys(i,j),
-- such that (s =pc t with (i j)) 
--            and (pij(queue(s)) = queue(t))
-- that is  ((pc(s,i) = pc(t,i)) and (pc(s,j) = pc(t,j)))
--          and (pij(queue(s)) = queue(t))
--
-- there are only following six cases 
-- for the term s' of depth n+1 
-- which represent all possible next states of s 
-- notice that k is Pid different from i or j
-- and by symmetry either i or j can be chosen
-- --> s'=want(s,k)
-- --> s'=try(s,k)
-- --> s'=exit(s,k)
-- --> s'=want(s,i)
-- --> s'=try(s,i)
-- --> s'=exit(s,i)

--> s'=want(s,k),c-want(s,k)
open QLOCKpij
-- arbitrary constants
op k : -> PidConst .
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- conditions
eq c-want(s,k) = true .
-- existance of t'
ops s' t' : -> Sys .
eq s' = want(s,k) .
eq t' = t .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t')) .
close
--> s'=want(s,k),~c-want(s,k)
open QLOCKpij
-- arbitrary constants
op k : -> PidConst .
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- conditions
eq c-want(s,k) = false .
-- existance of t'
ops s' t' : -> Sys .
eq s' = want(s,k) .
eq t' = t .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t')) .
close
--> s'=try(s,k),c-try(s,k)
open QLOCKpij
-- arbitrary constants
op k : -> PidConst .
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- conditions
eq c-try(s,k) = true .
-- existance of t'
ops s' t' : -> Sys .
eq s' = try(s,k) .
eq t' = t .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t')) .
close
--> s'=try(s,k),~c-try(s,k)
open QLOCKpij
-- arbitrary constants
op k : -> PidConst .
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- conditions
eq c-try(s,k) = false .
-- existance of t'
ops s' t' : -> Sys .
eq s' = try(s,k) .
eq t' = t .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t')) .
close
--> s'=exit(s,k),c-exit(s,k)
open QLOCKpij
-- arbitrary constants
op k : -> PidConst .
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- conditions
-- eq c-exit(s,k) = true .
eq pc(s,k) = cs .
--
op q : -> Queue .
-- lemma: csQtop(s,k)
--  ((pc(s,k) = cs) implies (queue(s) = q,k)) 
-- implies the following eq
eq queue(s) = q,k .
-- existance of t'
ops s' t' : -> Sys .
eq s' = exit(s,k) .
eq t' = t .
-- |- 
red ((pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
                         and (pij(queue(s')) = queue(t'))) .
close
--> s'=exit(s,k),~c-exit(s,k)
open QLOCKpij
-- arbitrary constants
op k : -> PidConst .
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- conditions
eq c-exit(s,k) = false .
-- existance of t'
ops s' t' : -> Sys .
eq s' = exit(s,k) .
eq t' = t .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t')) .
close
--> s'=want(s,i),c-want(s,i)
open QLOCKpij
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- condition
-- eq c-want(s,i) = true .
eq pc(s,i) = rm .
-- existance of t'
ops s' t' : -> Sys .
eq s' = want(s,i) .
eq t' = want(t,i) .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t')) .
close
--> s'=want(s,i),~c-want(s,i)
open QLOCKpij
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- condition
-- eq c-want(s,i) = false .
eq (pc(s,i) = rm) = false .
-- existance of t'
ops s' t' : -> Sys .
eq s' = want(s,i) .
eq t' = want(t,i) .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t')) .
close
--> s'=try(s,i),c-try(s,i)
open QLOCKpij
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- condition
-- eq c-try(s,i) = true .
eq pc(s,i) = wt .
eq top(queue(s)) = i .
-- ""eq top(queue(s)) = i ." justifies "eq queue(s)= q,i ."
op q : -> Queue .
eq queue(s)= q,i .
-- existence of t'
ops s' t' : -> Sys .
eq s' = try(s,i) .
eq t' = try(t,i) .  
-- |- 
red ((pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t'))) .
close
--> s'=try(s,i),~c-try(s,i)
open QLOCKpij
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- condition
eq c-try(s,i) = false .
-- existance of t'
ops s' t' : -> Sys .
eq s' = try(s,i) .
eq t' = t .
-- |- 
red ((pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t'))) .
close
--> s'=exit(s,i),c-exit(s,i)
open QLOCKpij
-- arbitrary constants
ops i j : -> PidConst .
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- condition
-- eq c-exit(s,i) = true .
eq pc(s,i) = cs .
-- "eq pc(s,i) = cs ." implies "eq queue(s) = q,i ."
-- by lemma csQtop
op q : -> Queue .
eq queue(s)= q,i .
-- existance of t'
ops s' t' : -> Sys .
eq s' = exit(s,i) .
eq t' = exit(t,i) .
-- |- 
red (pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j))
      and (pij(queue(s')) = queue(t')) .
close
--> s'=exit(s,i),~c-exit(s,i)
open QLOCKpij
-- induction hypothesis
ops s t : -> Sys .
eq pc(t,i) = pc(s,i) .
eq pc(t,j) = pc(s,j) .
eq queue(t) = pij(queue(s)) .
-- condition
-- eq c-exit(s,i) = false .
eq (pc(s,i) = cs) = false .
-- existance of t'
ops s' t' : -> Sys .
eq s' = exit(s,i) .
eq t' = exit(t,i) .
-- |- 
red ((pc(s',i) = pc(t',i)) and (pc(s',j) = pc(t',j)) 
     and (pij(queue(s')) = queue(t'))) .
close
-- QED
