-- ==========================================================
--> falsificationBySearch.mod
-- ==========================================================

in qlockTrans.mod
in mex.mod

set always memo on
clean memo

-- %%%%%%%%%%%%%
-- 2 agents case
-- %%%%%%%%%%%%%

-- falsification for 2 agents case
open (QLOCKijTrans + MEX)

-- try to find counter example for mutual exclusion property
red < init > =(1,5)=>* < S:Sys > 
      suchThat (not mutualEx(S,i,j)) .
red < init > =(1,6)=>* < S:Sys > 
      suchThat (not mutualEx(S,i,j)) .

-- check that mutualEx(S,i,j) holds upto some depth
red < init > =(*,5)=>* < S:Sys > 
      suchThat mutualEx(S,i,j) .
red < init > =(*,6)=>* < S:Sys > 
      suchThat mutualEx(S,i,j) .

-- find counter examples
red < init > =(1,5)=>* < S:Sys > 
      suchThat 
      (not ((top(queue(S)) = i) implies (pc(S,i) = wt)) and
           ((top(queue(S)) = j) implies (pc(S,j) = wt))) .

close

-- %%%%%%%%%%%%%
-- 3 agents case
-- %%%%%%%%%%%%%

-- verification of non existence of counter examples
-- for 3 agents case
open (QLOCKijkTrans + MEX)

-- try to find counter example for mutual exclusion property
red < init > =(1,5)=>* < S:Sys > 
      suchThat (not (mutualEx(S,i,j) and
                     mutualEx(S,i,k) and
                     mutualEx(S,j,k))) .
red < init > =(1,6)=>* < S:Sys > 
      suchThat (not (mutualEx(S,i,j) and
                     mutualEx(S,i,k) and
                     mutualEx(S,j,k))) .

-- check that mutualEx(S,i,j) holds upto some depth
red < init > =(*,5)=>* < S:Sys > 
      suchThat (mutualEx(S,i,j) and
                mutualEx(S,i,k) and
                mutualEx(S,j,k)) .
red < init > =(*,6)=>* < S:Sys > 
      suchThat (mutualEx(S,i,j) and
                mutualEx(S,i,k) and
                mutualEx(S,j,k)) .

close
