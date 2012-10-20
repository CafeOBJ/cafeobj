-- ==========================================================
--> verificationBySearchWithObEq.mod
-- ==========================================================

in qlockTrans.mod
in qlockObEq.mod
in mex.mod

set always memo on
clean memo

-- %%%%%%%%%%%%%
-- 2 agents case
-- %%%%%%%%%%%%%

-- verification of non existence of counter examples
-- for 2 agents case
open (QLOCKijTrans + QLOCKobEq + MEX)

-- defining observational/behavioral equivalence
pred _=ob=_ : Config Config {memo} .
vars S1 S2 : Sys .
eq (< S1 > =ob= < S2 >) = (S1 =ob= S2 with (i j)) .

-- try to find counter examples using ObEq
red < init > =(*,6)=>* < S:Sys > 
       suchThat (not mutualEx(S,i,j))
       withStateEq (C1:Config =ob= C2:Config) .
red < init > =(*,10)=>* < S:Sys > 
       suchThat (not mutualEx(S,i,j))
       withStateEq (C1:Config =ob= C2:Config) .

-- check that the number of 
-- the classes of observational equivlant states is finite 
red < init > =(*,*)=>* < S:Sys > 
       withStateEq (C1:Config =ob= C2:Config) .

-- proof of non-existence of counter examples
-- for 2 agents/processes case
red < init > =(*,*)=>* < S:Sys > 
       suchThat (not mutualEx(S,i,j))
       withStateEq (C1:Config =ob= C2:Config) .

-- proof of other properties
-- for 2 agents/processes case
red < init > =(*,*)=>* < S:Sys > 
       suchThat 
         (not (((pc(S,i) = wt) implies (i in queue(S))) and
               ((pc(S,j) = wt) implies (j in queue(S)))))
       withStateEq (C1:Config =ob= C2:Config) .
red < init > =(*,*)=>* < S:Sys > 
       suchThat 
         (not (((top(queue(S)) = i) implies 
                    ((pc(S,i) = wt) or (pc(S,i) = cs))) and
               ((top(queue(S)) = j) implies 
                    ((pc(S,j) = wt) or (pc(S,j) = cs))))) 
       withStateEq (C1:Config =ob= C2:Config) .
red < init > =(*,*)=>* < S:Sys > 
       suchThat 
         (not (((pc(S,i) = cs) implies (top(queue(S)) = i)) and
               ((pc(S,j) = cs) implies (top(queue(S)) = j))))
       withStateEq (C1:Config =ob= C2:Config) .

close

-- %%%%%%%%%%%%%
-- 3 agents case
-- %%%%%%%%%%%%%

-- verification of non existence of counter examples
-- for 3 agents case
open (QLOCKijkTrans + QLOCKobEq + MEX)

-- defining observational/behavioral equivalence
pred _=ob=_ : Config Config {memo} .
vars S1 S2 : Sys .
eq (< S1 > =ob= < S2 >) = (S1 =ob= S2 with (i j k)) .

-- try to find counter examples using ObEq
red < init > =(*,6)=>* < S:Sys > 
       suchThat 
        (not (mutualEx(S,i,j) and
              mutualEx(S,i,k) and
              mutualEx(S,j,k)))
       withStateEq (C1:Config =ob= C2:Config) .
red < init > =(*,10)=>* < S:Sys > 
       suchThat
        (not (mutualEx(S,i,j) and
              mutualEx(S,i,k) and
              mutualEx(S,j,k)))
       withStateEq (C1:Config =ob= C2:Config) .

-- check that the number of 
-- the classes of observational equivlant states is finite 
red < init > =(*,*)=>* < S:Sys > 
       withStateEq (C1:Config =ob= C2:Config) .

-- verification of non-existence of counter examples
-- for 3 agents/processes case
red < init > =(*,*)=>* < S:Sys > 
       suchThat 
        (not (mutualEx(S,i,j) and
              mutualEx(S,i,k) and
              mutualEx(S,j,k)))
       withStateEq (C1:Config =ob= C2:Config) .

-- verification of other properties
-- for 2 agents/processes case
red < init > =(*,*)=>* < S:Sys > 
       suchThat 
         (not (((pc(S,i) = wt) implies (i in queue(S))) and
               ((pc(S,j) = wt) implies (j in queue(S))) and
               ((pc(S,k) = wt) implies (k in queue(S)))))
       withStateEq (C1:Config =ob= C2:Config) .
red < init > =(*,*)=>* < S:Sys > 
       suchThat 
         (not (((top(queue(S)) = i) implies 
                    ((pc(S,i) = wt) or (pc(S,i) = cs))) and
               ((top(queue(S)) = j) implies 
                    ((pc(S,j) = wt) or (pc(S,j) = cs))) and
               ((top(queue(S)) = k) implies 
                    ((pc(S,k) = wt) or (pc(S,k) = cs)))))
       withStateEq (C1:Config =ob= C2:Config) .
red < init > =(*,*)=>* < S:Sys > 
       suchThat 
         (not (((pc(S,i) = cs) implies (top(queue(S)) = i)) and
               ((pc(S,j) = cs) implies (top(queue(S)) = j)) and
               ((pc(S,k) = cs) implies (top(queue(S)) = k))))
       withStateEq (C1:Config =ob= C2:Config) .

close
