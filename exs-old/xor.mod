** -*- Mode:CafeOBJ -*-

module! BEH {
  extending  (PROPC)
  ops i1 i2 p1 p2 p3 o : -> Prop 
  eq p1 = not i1 .
  eq o = i1 xor i2 .
  eq p2 = true .
  eq p3 = false .
}

** p1 = p2 if not i1 .
module! BEH1 {
  using (BEH)
  eq i1 = false .
}

reduce in BEH1 : p1 == p2 .

** p1 = p3 if i1 .
module! BEH2 {
  using (BEH)
  eq i1 = true .
}
--> reduce p1 == p3 .
reduce in BEH2 : p1 == p3 .

** o = i1 if not i2 .
module! BEH3 {
  using (BEH)
  eq i2 = false .
}

reduce in BEH3 : o == i1 .

** o = p1 if i2 .
module! BEH4 {
  using (BEH)
  eq i2 = true .
}

reduce in BEH4 : o == p1 .

** o = i2 if not i1 .
module! BEH5 {
  using (BEH)
  eq i1 = false .
}

reduce in BEH5 : o == i2 .
** o = i2 if p1 .
module! BEH6 {
  using (BEH)
  eq i1 = false .
}

reduce in BEH6 : o == i2 .

module! BEH' {
  ex (PROPC)
  ops p1 p2 q : -> Prop 
  eq p1 = not q .
  eq p2 = q .
}

** p1 = true if not p2 .
module! BEH1 {
  using (BEH')
  eq q = false .
}

reduce in BEH1 : p1 == true .

** p1 = false if p2 .
module! BEH2 {
  using (BEH')
  eq q = true .
}

reduce in BEH2 : p1 == false .

** p2 = true if not p1 .
module! BEH3 {
  using (BEH')
  eq q = true .
}

reduce in BEH3 : p2 == true .

** p2 = false if p1 .
module! BEH4 {
  using (BEH')
  eq q = false .
}

reduce in BEH4 : p2 == false .
--
eof
--
$Id: xor.mod,v 1.1.1.1 2003-06-19 08:30:18 sawada Exp $
