-- ==========================================================
--> mex.mod
-- ==========================================================

-- mutual exclusion property
mod* MEX {
 inc(QLOCK)
 pred mutualEx : Sys Pid Pid 
 var S : Sys . vars I J : Pid .
 eq mutualEx(S,I,J) 
    = ((pc(S,I) = cs) and (pc(S,J) = cs)) implies (I = J) .
} 
