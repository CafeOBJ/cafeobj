** -*- Mode:CafeOBJ -*-
** NOTE this example does not uses hidden sort.
** you can find hidden sorted version in "flag.mod"
**> prove \foall F. rev rev F = F behaviorally satisfied in FLAG

module! FLAG {
  protecting (PROPC)
  [ Flag ]
  op newf : -> Flag
  ops (up_) (dn_) (rev_) : Flag -> Flag
  op up?_ : Flag -> Prop
  var F : Flag
  eq up? up F = true .
  eq up? dn F = false .
  eq up? rev F = not up? F .
  eq up? newf = false .
}

**> define a relation R:
module* R {
  protecting (FLAG)
  op _R_ : Flag Flag -> Bool
  --
  vars F F' : Flag
  eq F R F' = up? F == up? F .
}

**> show it is a bhavioral congruence:
open R .
ops f f' : -> Flag .
eq up? f = up? f' .
red up f R up f' .
red dn f R dn f' .
red rev f R rev f' .
close

**> now prove the equation:
open R .
op f : -> Flag .
red rev rev f R f .
close

--
eof
**
$Id: beh-sat.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
