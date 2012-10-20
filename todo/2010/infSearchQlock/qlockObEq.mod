-- ==========================================================
--> file: qlockObEq.mod
-- ==========================================================

-- qlock.mod is assumed
-- in qlock.mod

-- generic list
mod! LIST (X :: TRIV) {
 [Elt < List]
 op (_ _) : Elt List -> List {constr r-assoc}
}

make PIDlist ((LIST(PID{sort Elt -> Pid}))*{sort List -> PidList})

mod* QLOCKobEq {
  inc(QLOCK + PIDlist)

-- definition of (S1:Sys =ob= S2:Sys) 
  pred (_=ob=_with_) : Sys Sys PidList {memo} 
  pred (_=pc_with_) : Sys Sys PidList 

  vars S1 S2 : Sys .
  var P : Pid .
  var PL : PidList .

  eq (S1 =pc S2 with P) = (pc(S1,P) = pc(S2,P)) .
  eq (S1 =pc S2 with (P PL)) = (pc(S1,P) = pc(S2,P)) 
                                and (S1 =pc S2 with PL) .
  eq (S1 =ob= S2 with PL) = (S1 =pc S2 with PL) 
                             and (queue(S1) = queue(S2)) .
}
