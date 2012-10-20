-- "op none : -> ?Pid" and "Elt < List"

mod* PID {
  [Pid]
  op none : -> ?Pid
  op _=_ : Pid Pid -> Bool {comm}
  var I : Pid
  eq (I = I) = true .
  eq (I = none) = false .
--  eq (none = none) = true .
}

mod! LIST (X :: TRIV) {
 [Elt < List]
 op (_ _) : Elt List -> List {constr} .
}

mod! PIDlist {pr((LIST(PID{sort Elt -> Pid}))*{sort List -> PidList})}

eof

-- after 

PIDlist> describe op none
======================================================================
name                : none/0
module              : PID
number of arguments : 0
default attributes  :
 rewrite strategy   : not specified
 syntax             :
   precedence       : not specified
   computed prec.   : 0
   form             : "none" 
 theory             : 
----------------------------------------------------------------------
rank                : -> ?PidList
  module            : LIST(X <= PID{sort (%sort-ref Elt) -> (%sort-ref Pid)
   }) * {sort (%sort-ref List) -> (%sort-ref PidList)}
  theory            : 
  rewrite strategy  : nil
  precedence        : 0
  derived from      : ("none") of PID
  axioms            :
----------------------------------------------------------------------
rank                : -> ?Pid
  module            : PID
  theory            : 
  rewrite strategy  : nil
  precedence        : 0
  axioms            :
PIDlist> 

{
rank                : -> ?PidList
...
  derived from      : ("none") of PID
}

should be a problem?
