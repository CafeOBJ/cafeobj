-- Return-Path: dlucanu@infoiasi.ro 
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id BAA09600 for <sawada@sras75.sra.co.jp>; Thu, 17 Jul 1997 01:41:27 +0900
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8]) by srasva.sra.co.jp (8.6.12+2.4W3/3.4W-srambox) with ESMTP id BAA26374 for <sawada@srasva.sra.co.jp>; Thu, 17 Jul 1997 01:41:07 +0900
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14]) by sranha.sra.co.jp (8.6.13/3.4W-sranha) with ESMTP id BAA16930 for <sawada@sra.co.jp>; Thu, 17 Jul 1997 01:38:48 +0859
-- Received: from thor.infoiasi.ro by sraigw.sra.co.jp (8.6.13/3.4W-sraigw)
--	id BAA09891; Thu, 17 Jul 1997 01:40:08 +0900
-- Received: from [193.226.30.151] (it1.infoiasi.ro [193.226.30.151])
--	by thor.infoiasi.ro (8.8.5/8.8.5) with SMTP id QAA06550;
--	Wed, 16 Jul 1997 16:38:42 GMT
-- Message-Id: <199707161638.QAA06550@thor.infoiasi.ro>
-- To: Diaconescu Razvan <diacon@stoilow.imar.ro>,
--        "sawada@sra.co.jp" <sawada@sra.co.jp>,
--        "s_iida@jaist.ac.jp" <s_iida@jaist.ac.jp>,
--        "vec@moisil.math.ro" <vec@moisil.math.ro>,
--        Virgil Emil Cazanescu <vec@math.math.unibuc.ro>,
--        Michihiro Matumoto <mitihiro@jaist.ac.jp>,
--        "kokichi@jaist.ac.jp" <kokichi@jaist.ac.jp>,
--        Gheorghe Stefanescu <ghstef@stoilow.imar.ro>,
--        "stefanes@informatik.tu-muenchen.de" <stefanes@informatik.tu-muenchen.de>
-- Subject: unreliable buffers example
-- Date: Wed, 16 Jul 97 19:35:06 -0500
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- X-Mailer: E-Mail Connection v2.5.02
-- Content-Type: text
-- Content-Length: 8475

-- [ From: Dorel Lucanu * EMC.Ver #2.5.02 ] --

-- Dear Colleagues,

-- Bellow you find a CafeOBJ specification for unreliable buffers. This example
-- is very close 
-- to  the component unreliable queue (channel) of the ABP example.  I hope you
-- will enjoy it. 
-- I think that many things can be simplified, corrected or completed.
-- Therefore any comments  
-- will be greatly appreciated.

-- Best regards,
-- Dorel.

-- ***************UNRELIABLE BUFFERS**************************

-- This example is inspired from "Behaviour-Refinement of Coalgebraic
-- Specification with   
-- Coinductive -- Correctness Proofs" by Bart Jacobs, to appear in the
-- Proceedings of   
-- TAPSOFT/FASE 1997 (the original example  is due to  M. Broy).
--
-- We consider buffers which can be empty or contain a single element. An
-- unreliable buffer is 
-- a buffer with the property that the putting of an element in it may fail. We
-- consider here only
-- fair buffers (they may not fail infinitely many times). We define a module
-- BUFFER which specify a "reliable" buffer and a module UBUFFER which describe
-- an
-- unreliable buffer. Next we define an extra-level of the unreliable buffer,
-- namely the module
-- XUBUFFER, which contains moreover two derived operators. Using these two
-- operators (in fact 
-- only the first one is important) we can describe the fairness property. The
-- aim is to show that
-- the unreliable buffer XUBUFFER refines the reliable buffer BUFFER (and hence
-- it is correct).
-- The refinement is proved in two ways. The first one follows the idea
-- suggested in "Hidden
-- Agenda".  The module PROOF defines the environment for this proof. The proof
-- is included
-- in  the file TST-BUFFERS.
-- The second way uses a bisimulation relation as that defined by B. Jacobs. We
-- think that we 
-- have to prove that this method is consistent with the definition of the
-- refinement given in "Hidden
-- Agenda". This is that what we try to do in the next future. The module
-- PROOF1 defines the
-- environment for this proof. The proof is included in the file TST1-BUFFERS.

-- We think that this (very interesting) example (could) exhibits two important
-- CafeOBJ features:
--  - new strategies to prove the refinement
--  - how we can manipulate the fairness property
--
-- Remark. The last equation in TST-BUFFERS cannot be proved due to a limit of
-- the system  (we have got the  error message "Value stack overflow").

-- ************************MODULES*******************************************
mod ELT
{
  [Elt]
  op nothing : -> Elt
}

mod* BUFFER(X :: ELT)
{
  *[Buffer]*
  op init : -> Buffer
  bop push : Buffer Elt -> Buffer
  bop empty : Buffer -> Buffer
  bop display : Buffer ->  Elt

  var B : Buffer
  var E : Elt

  eq display(init) = nothing .
  eq display(empty(B)) = nothing .
  ceq display(push(B,E)) = display(B) if display(B) =/= nothing .
  ceq display(push(B,E)) = E if display(B) == nothing .
}


mod! ACKNOWLEDGE
{
  [Acknowledge]
  ops yes no : ->  Acknowledge
}

**>  UBUFFER

mod* UBUFFER(X :: ELT)
{
  protecting (ACKNOWLEDGE + NAT)

  *[UBuffer]*

  op init : -> UBuffer
  bop put : UBuffer Elt -> UBuffer
  bop empty : UBuffer -> UBuffer
  bop display : UBuffer ->  Elt
  bop ackn : UBuffer -> Acknowledge

  var UB : UBuffer
  var E : Elt
  var N : Nat

  eq ackn(init) = no .

  eq display(init) = nothing .
  eq display(empty(UB)) = nothing .
  ceq display(put(UB, E)) = display(UB) if (display(UB) =/= nothing) or
                                         (ackn(put(UB,E)) == no) .
  ceq display(put(UB, E)) = E if (display(UB) == nothing) and
                                (ackn(put(UB, E)) == yes) .
}


mod* XUBUFFER(X :: ELT)
{
  protecting (UBUFFER(X))

  bop put_in_of_times : Elt UBuffer Nat -> UBuffer
  bop push : UBuffer Elt -> UBuffer

  var UB : UBuffer
  var E : Elt
  var N : NzNat

-- the definition of put_in_of_times

  eq   put E in UB of 0 times = UB .
  ceq  put E in UB of N times = put(put E in UB of (p N) times, E) if (N > 0
) .
  ceq ackn(put E in UB of (p N) times) = no if ackn(put E in UB of N times)
== no .

-- the definition of push

  ceq push(UB, E) = put(UB, E) if display(UB) =/= nothing .
  ceq push(put E in UB of N times, E) = push(put E in UB of (s N) times, E)
if
                 ackn(put E in UB of N times) == no .
  ceq push(put E in UB of N times, E) = put E in UB of N times if
                 ackn(put E in UB of N times) == yes .
}





mod PROOF(X :: ELT)
{
  protecting (XUBUFFER(X))

-- constants for universal quantifiers

  ops e e1 e2 : -> Elt
  ops n n1 n2 : -> NzNat
  ops ub ub1 ub2 : -> UBuffer

-- The relation R is defined on XUBUFFER as follows:

  op _R_ : UBuffer UBuffer -> Bool

  vars UB1 UB2 : UBuffer

  eq (UB1 R UB2) = (display(UB1) == display(UB2)) .

-- assumption

  eq display(ub1) = display(ub2) .
}




mod PROOF1(X :: ELT)
{
  protecting (BUFFER(X) + XUBUFFER(X))

-- The relation R is a "bisimulation" between XUBUFFER and BUFFER and is
-- defined as
-- follows:
--     op _R_ : UBuffers Buffers -> Bool
--     UB R B  = true iff display(UB) == display(B)


  op _R_ : UBuffer Buffer -> Bool


  var B : Buffer
  var UB : UBuffer

  eq UB R B = (display(UB) == display(B)) .

-- constants for universal quantifiers

  ops e e1 e2 : -> Elt
  op n : -> NzNat
  op b : -> Buffer
  op ub : -> UBuffer

-- assumption

  eq display(ub) = display(b) .

}

-- **********************file TST-BUFFERS*******************************
-- This file contains a proof of the fact "XUBUFFER refines BUFFER" using
-- the method
-- suggested in "Hidden Agenda".

-- We firstly show that R is a congruence

-- prove the compatibility with the operator "push":

-- -- case 1: display(ub1) = display(ub2) =/= nothing

open PROOF
eq (display(ub1) == nothing) = false .
eq (display(ub2) == nothing) = false .
red push(ub1, e) R push(ub2, e) . -- it should be true
close

-- -- case 2 : push(ub1,e) = put e in ub1' of n1 times and
--             push(ub2,e) = put e in ub2' of n2 times and
--             ub1' R ub2'

open PROOF
ops ub1' ub2' : -> UBuffer .
eq display(ub1') = display(ub2') .
eq ub1 = put e in ub1' of n1 times .
eq ackn(put(put e in ub1' of (p n1) times, e)) = yes .
eq display(put e in ub1' of (p n1) times) = nothing .
eq ub2 = put e in ub2' of n2 times .
eq ackn(put(put e in ub2' of (p n2) times, e)) = yes .
eq display(put e in ub2' of (p n2) times) = nothing .

red push(ub1, e) R push(ub2, e) . -- it should be true
close

-- prove the compatibility with the operator "empty":

open PROOF
red empty(ub1) R  empty(ub2) . -- it should be true
close

-- Now we prove the BUFFER equations

-- -- case 1

open PROOF
eq (display(ub) == nothing) = false .

red display(push(ub, e)) == display(ub) . -- it should be true
close

-- -- case 2

open PROOF
eq ub = put e in ub of n times .
eq ackn(put(put e in ub of (p n) times, e)) = yes .
eq display(put e in ub of (p n) times) = nothing .

**  -----------------------------
eof

red display(push(ub, e)) == e . -- it should be true
close


-- Remark. The proofs of the other equations are evident.

***************************file TST1-BUFFERS*********************
-- This file contains a proof of the fact "XUBUFFER refines BUFFER" using a
-- bisimulation relation
-- R defined as in "Behaviour-Refinement of Coalgebraic Specification with
-- Coinductive
-- Correctness Proofs" by Bart Jacobs, to appear in the Proceedings of
-- TAPSOFT/FASE
-- 1997.
-- A theoretical foundation in the terms of the definition for refinement
-- given in "Hidden agenda"
-- follows to be given.

-- -----------
-- Lemma 1 --
-- -----------

-- We show that init.Buffer R init.UBuffer

open PROOF1
red init R init . -- it should be true
close

-- -----------
-- Lemma 2 --
-- -----------

-- We show that if ub R b then empty(b) R empty(b)

open PROOF1
red  empty(ub) R empty(b) . -- it should be true
close

-- -----------
-- Lemma 3 --
-- -----------

-- We show that if ub R b and display(ub) =/= nothing =/= display(b) then
-- push(ub) R push(b)

open PROOF1
eq (display(ub) == nothing) = false .
eq (display(b) == nothing) = false .

red  push(ub, e) R push(b, e) . -- it should be true
close

-- -----------
-- Lemma 4 --
-- -----------

-- We show that if ub R b and display(ub) == nothing == display(b) then push
-- (ub) R push(b).
-- We recall that push(ub, e) = put e in ub of n times (see the module PROOF
-- )

open PROOF1
eq display(ub) = nothing .
eq display(b) = nothing .
eq  ackn(put e in ub of (p n) times) = no .
eq  ackn(put(put e in ub of (p n) times, e)) = yes .
eq  display(put e in ub of (p n) times) = nothing .

red  (put e in ub of n times) R push(b, e) . -- it should be true
close

eof


