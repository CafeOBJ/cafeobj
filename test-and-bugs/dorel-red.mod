-- Date: Fri, 3 Oct 1997 21:06:04 +0300 (EET DST)
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- Reply-To: Dorel Lucanu <dlucanu@infoiasi.ro>
-- To: Toshimi Sawada <sawada@sra.co.jp>
-- Subject: problems with reduce coomand
-- In-Reply-To: <199710010520.OAA19161@sras75.sra.co.jp>
-- Message-ID: <Pine.LNX.3.95.971003205318.29242A-100000@thor.infoiasi.ro>
-- MIME-Version: 1.0
-- Content-Type: TEXT/PLAIN; charset=US-ASCII
-- Content-Length: 3179

-- Dear Toshimi,

-- Please take a look on the below proof score. It seems to be a bug in
-- executing reduce coomand. Because the computer I usually use is broken, I
-- am still working with the version 1.3.1. May be this problem is already
-- corrected in the new version 1.4. If this is the case, I appologize for
-- the inconveninets due to this message.

-- With warmest regards,
-- Dorel.

-- ************************

-- CafeOBJ> open VM||CL
-- -- opening module VM||CL.. done.

-- %VM||CL> op s : -> St .

-- %VM||CL> let t = des(p-m(cl s)) .
-- _
-- -- setting let variable "t" to :
--     des(p-m((cl s))) : Item

-- %VM||CL> eq t = tea .

-- %VM||CL> red t .
-- *
-- * system failed to prove =*= is a congruence on hidden sort Cl. 
-- * system failed to prove =*= is a congruence on hidden sort Vm. 
-- * system already proved =*= is a congruence on hidden sort St. 
-- -- reduce in % : des(p-m(cl s))
-- des(p-m(cl s)) : Item
-- (0.000 sec for parse, 0 rewrites(0.000 sec), 2 match attempts)

-- %VM||CL> start t .

-- %VM||CL> apply red at term
-- result des(p-m(cl s)) : Item

-- %VM||CL> apply 13 at term .
-- result tea : Item

-- %VM||CL> 

-- %VM||CL> show term t
-- des(p-m((cl s))) : Item

-- %VM||CL> op s1 : -> St .

-- %VM||CL> eq des(p-m(cl s)) = tea .
-- _

-- %VM||CL> red des(p-m(cl s)) .
-- *
-- * system failed to prove =*= is a congruence on hidden sort Cl. 
-- * system failed to prove =*= is a congruence on hidden sort Vm. 
-- * system already proved =*= is a congruence on hidden sort St. 
-- -- reduce in % : des(p-m(cl s))
-- des(p-m(cl s)) : Item
-- (0.010 sec for parse, 0 rewrites(0.000 sec), 2 match attempts)

-- %VM||CL> start des(p-m(cl s)) .

-- %VM||CL> apply reduce at term .
-- result des(p-m(cl s)) : Item

-- %VM||CL> 

-- %VM||CL> apply .13 at term
-- result tea : Item

-- %VM||CL> q
-- [Leaving CafeOBJ]
-- ********************VM-CL.MOD FILE***********
mod! DATA {
  [ Item  Feeling ]
  ops coffee tea   :         -> Item
  ops happy disapp :         -> Feeling
  op not_          : Item    -> Item
  op not_          : Feeling -> Feeling
  eq not coffee = tea .
  eq not tea = coffee .
  eq not happy = disapp .
  eq not disapp = happy .
}

mod* VM {
  protecting (DATA)
  *[ Vm ]*
  op init :    -> Vm
  bop out : Vm -> Item
  bop r-m : Vm -> Vm
}

mod* BROKEN-VM {
  protecting(VM)
  var V : Vm
  eq out(r-m(V)) = coffee .
}

mod* CL {
  protecting(DATA)
  *[ Cl ]*
  op init      :    -> Cl
  bops w p-m   : Cl -> Cl
  bops des get : Cl -> Item
  bop feel     : Cl -> Feeling
  var C : Cl
  ceq feel(p-m(C)) = happy if des(p-m(C)) == get(p-m(C)) .
  ceq feel(p-m(C)) = disapp if des(p-m(C)) =/= get(p-m(C)) .
}

mod* VM||CL {
  protecting(BROKEN-VM + CL)
  *[ St ]*  
  op init     :    -> St
  bop p&r-m   : St -> St
  bop vm_     : St -> Vm
  bop cl_     : St -> Cl
  bop out&get : St -> Item

  var S : St

-- equations for synchronization
  eq vm p&r-m(S) = r-m(vm S) .
  eq vm init = init .
  eq cl p&r-m(S) = p-m(cl S) .
  eq cl init = init .
  eq out&get(p&r-m(S)) = out(r-m(vm S)) . 
--  eq get(cl p&r-m(S)) = get(cl p-m(S)) . -- it is a consequence
  eq get(p-m(cl S)) = out&get(p&r-m(S)) .
--  eq des(cl p&r-m(S)) = des(cl p-m(S)) . -- it is a consequence
--  eq feel(cl p&r-m(S)) = feel(cl p-m(S)) . -- it is a consequence
}
-- *******************************************



