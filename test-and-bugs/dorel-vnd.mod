-- Date: Sat, 4 Oct 1997 14:55:46 +0300 (EET DST)
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- To: Razvan Diaconescu <diacon@jaist.ac.jp>
-- cc: ishisone@sra.co.jp, kokichi@jaist.ac.jp, nakagawa@sra.co.jp,
--         ogata@jaist.ac.jp, s_iida@jaist.ac.jp, sawada@sra.co.jp,
--         vec@funinf.math.unibuc.ro
-- Subject: Re: hidden vending machines with switch
-- In-Reply-To: <9709270827.AA09811@is27e0s07.jaist.ac.jp>
-- Message-ID: <Pine.LNX.3.95.971004143215.9417D-100000@thor.infoiasi.ro>
-- MIME-Version: 1.0
-- Content-Type: TEXT/PLAIN; charset=US-ASCII
-- Content-Length: 6633

-- Dear all,

-- Here is my opinion (in the spirit of "Understanding CafeOBJ by example") 
-- on how we can handle the concurrent connection in CafeOBJ. 

-- Following ha, a concurrent connection consists of a synchronization and a
-- connection. A synchronization of two specifications SP1 and SP2 aconsists
-- of:
--   -- a shared specification SP,
--   -- and two synchronization signature morphisms 
--           \phi_1: SP \to SP1 and \phi_2: SP \to SP2
-- We call the images methods (attributes) in SP by \phi_i the synchronization
-- methods (attributes). The other operations will be called indepenedent
-- operations.
-- A connection of a synchronization consists of:
--   -- a specification CSP called concurrent specification, and
--   -- two refinements \psi_1: SP1 \to CSP and \psi_2: SP2 \to CSP
-- which must satisfy the commutativity equations.

-- So, the construction  of  a concurrent connection SP1 || SP2 in CafeOBJ
-- follows the following steps:
--   1. Establish the synchronization of the two specifications. This consists
-- in pointing out the synchronization methods and attributes in SP1 and SP2,
-- respectively. Generally, we
-- do not need to define a distinguished module for the shared part; its
-- definition will be deduced by dividing the operations from each
-- specification  in two
-- classes: synchronization operations and independent operations. The same
-- thing is true for the synchronization morphisms. These are very important
-- when we define the synchronization equations and the commutativity equations.

--   2. Define the concurrent connection CSP = SP1 || SP2. The main steps in
-- defining CSP are:
--     2.1. Import SP1 + SP2 in protecting way.
--     2.2. Add the projections pr1: CSP \to SP1 and pr2: CSP \to SP2. This
-- allows us to see a state of CSP as a sum pr1(S1) + pr2(S2), where S1 is a
-- SP1-state and S2 is a SP2-state.
--     2.3. Add the methods and the attributes of the concurrent connection.
--     2.4. Write the equations which defines a state of CSP as a sum of the
-- two component states (of SP1 and SP2, respectively). This is equivalent with
-- to say - by means of projections - how the CSP-methods reflect on the
-- components. 
--     2.5. Write the equations which say how the CSP-attributes are computed
-- from the attributes of the components. 
--     The equations 2.4 and 2.5 have also to reflect the synchronization. 
--     2.6. Add, eventually, new equations to define the nedeed properties of the
-- concurrent connection.
--   3. Prove that the concurrent connection is correct. This requires two
-- substeps:
--     3.1. Prove that CSP refines SP1 and SP2, respectively.
--     3.2. Prove the commutativity equations. Recall that these equations invoke
-- only the independent methods and attributes in SP1 and SP2. Often, this step 
-- requires  the adding of new equations in CSP.

-- Here is an example which specifies the interaction between a broken
-- vending machine ( it supplies always only coffee) and a client. We can
-- prove very simple facts: the clients gets always only coffee, if the
-- client desired tea then he is disappointed, etc. I will be happy if
-- someone else can find other interesting properties of this specification.

-- Best regards,
-- Dorel.
-- *******************************
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
-- ***************************
-- the synchronization specification consist of a constant 'init', a method
-- -- 'meth' and an attribute 'attr' 
-- the synchronization morphisms:
-- \phi_1
-- -- init |-> init
-- -- meth |-> r-m
-- -- attr |-> out
-- \phi_2
-- -- init |-> init
-- -- meth |-> p-m
-- -- attr |-> get
-- the connection:
-- \psi_1
-- -- init |-> init
-- -- r-m |-> pr-m
-- -- out |-> out&get
-- \psi_2
-- -- init |-> init
-- -- p-m |-> pr-m
-- -- get |-> out&get
-- -- des |-> des(cl_)
-- -- feel |-> feel(cl_)
-- it is easy to see that \phi_1;\psi_1 = \phi_2;\psi_2

-- prove that VM||CL refines BROKEN-VM and CL

open VM||CL
ops  s s1 s2 : -> St .

-- prove the equations in BROKEN-VM
red out(vm p&r-m(s)) == coffee .

-- prove the equations in CL
-- hyp
eq des(p-m(cl s1)) == get(p-m(cl s1)) = true .
eq des(p-m(cl s2)) =/= get(p-m(cl s2)) = true .

red feel(cl p&r-m(s1)) == happy . -- here is a bug in ver. 1.3.1
red feel(cl p&r-m(s2)) == disapp .  -- here is a bug in ver. 1.3.1
close

-- prove the commutativity eqns
-- -- the only operator which is not in the image of \phi_k is des
-- -- so there are no commutativity equations

-- prove that des(cl p&r-m(S)) = des(p-m(cl S)) and
--            opn(cl p&r-m(S)) = opn(p-m(cl S))
open VM||CL
op s : -> St .
red get(cl p&r-m(s)) == get(p-m(cl s)) . 
red des(cl p&r-m(s)) == des(p-m(cl s)) . 
red feel(cl p&r-m(s)) == feel(p-m(cl s)) . 
close

-- prove that the client is happy if he desired coffee
-- and is disappointed if he desired tea 

open VM||CL
op s : -> St .
-- hyp 
eq des(p-m(cl s)) = tea .

red feel(cl p&r-m(s)) == disapp . -- here is a bug in the version 1.3.1
close

open VM||CL
op s : -> St .
-- hyp 
eq  des(p-m(cl s)) = coffee .

red feel(cl p&r-m(s)) == happy . -- here is a bug in the version 1.3.1
close

-- prove that the client gets always coffee

open VM||CL
op s : -> St .

red get(cl p&r-m(s)) == coffee .
close
-- ********************************************

-- P.S. If you run this example under the version 1.3.1 then some equations
-- are not reduced as you expect. Probably, is a bug in this version of the
-- system.






