-- process identifiers
mod* PID {
  [Pid]
  op none : -> ?Pid -- error process id
  -- op _o=_ : Pid Pid -> Bool {comm}
  op _o=_ : ?Pid ?Pid -> Bool {comm}
  var I : Pid
  eq (I o= I) = true .
  eq (I o= none) = false .
  eq (none o= none) = false .
}

view TRIV2PID from TRIV to PID { sort Elt -> Pid }

mod! LIST (X :: TRIV) {
  [ Elt < List ]
  op (__) : Elt List -> List {constr}
}

**> PIDList1

make PIDList0 ((LIST(PID)))

-- make PIDList1 ((LIST(PID{sort Elt -> Pid})) * {sort List -> PidList})
-- mod PIDList2 {pr ((LIST(PID{sort Elt -> Pid})) * {sort List -> PidList})}
-- make PIDList3 ((LIST(X <= TRIV2PID)) * {sort List -> PidList})

eof
--

