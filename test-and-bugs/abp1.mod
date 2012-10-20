-- To: "sawada@sra.co.jp" <sawada@sra.co.jp>
-- Subject: CafeOBJ problems
-- Date: Tue, 20 May 97 07:39:31 -0500
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- X-Mailer: E-Mail Connection v2.5.02
-- Content-Type: text
-- Content-Length: 18259

-- [ From: Dorel Lucanu * EMC.Ver #2.5.02 ] --

-- Dear Sawada,

-- Below you find some problems I have  got while I worked with CafeOBJ system.
-- These problems were discussed  in our group with Shusaku Iida, Michihiro
-- Matumoto and Razvan Diaconescu and perhaps you already know them. In a
-- discussion with Razvan, he told me that is better as any problem be reported
-- to you; that is I try to do now. I appreciate very much your effort to do
-- such a complex system and I hope that my messages will help you in this
-- enterprising project.

-- ******************
-- **Problem 1. **
-- ******************
-- It seems to be a limit of the system. The two input files contain two
-- variant of the Shusaku's ABP example. The second file differ from the former
-- only by considerind "bop" instead of "op" in some modules (UNRELIABLE-FIFO-
-- CHANNEL, SENDER-RECEIVER, ...).


-- ****************DIALOGUE WITH CAFEOBJ**********************
-- Script started on Mon May 19 11:21:23 1997
-- bash$ ./cafeobj
-- -- loading standard prelude
-- [Error]: no such file: std
-- 
-- ** returning to top level
-- 
--                   -- CafeOBJ system Version 1.2.0 --
--                   built: 1997 Apr 20 Sun 15:55:59 GMT
--                           prelude file: NONE
--                                  ***
--                      1997 May 19 Mon 8:21:32 GMT
--                            Type ? for help
--                                  ---
--                      uses GCL (GNU Common Lisp)
--               Licensed under GNU Public Library License
--                 Contains Enhancements by W. Schelter
--
-- CafeOBJ> in abp1.txt
-- processing input : /home/dlucanu/cafeobj/cafeobj-1.2.0/bin/abp1.txt
-- defining module! QUEUE_.*........_.....* done.
-- defining module! NAT-QUEUE,,,,,,_,,*._* done.
-- defining module* MESSAGE._* done.
-- defining module! 2TUPLE_.*._.*......._..* done.
-- defining module! MES-BOOL,,,,,,_,,,,,,,,,_,,*._* done.
-- defining module! MES-QUEUE,,,,,,_,,,,,,,,,_,,*._* done.
-- defining module! ABP-DATA.,,,,,,_,,,,,,,,,_,,*.,,,,,,_,,,,,,,,,_,,*......
-- .._._* done.
-- defining module* UNRELIABLE-FIFO-CHANNEL_.*.,,,,,,_,,*........_...* done.
-- defining module* FIFO1,,,,,,,_,,*,,,,,_,,,,,,,,,_,,*._* done.
-- defining module* FIFO2,,,,,,,_,,*,,,,,_,,,,,,,,,_,,*._* done.
-- defining module* SENDER-RECEIVER.........._.......* done.
-- defining module* SENDER,,,,,,,_
-- Error: The index, 4, is too large
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by CAFEOBJ-EVAL-MODULE-PROC.
-- Broken at EVAL-IMPORT-MODEXP.  Type :H for Help.
-- CHAOS>>:q
--
-- CafeOBJ> in abp1_1.txt
-- -- processing input : /home/dlucanu/cafeobj/cafeobj-1.2.0/bin/abp1_1.txt
-- -- defining module! QUEUE
-- [Warning]: redefining module QUEUE _.*........_.....* done.
-- defining module! NAT-QUEUE
-- [Warning]: redefining module NAT-QUEUE ,,,,,,_,,*._* done.
-- defining module* MESSAGE
-- [Warning]: redefining module MESSAGE ._* done.
-- defining module! 2TUPLE
-- [Warning]: redefining module 2TUPLE _.*._.*......._..* done.
-- defining module! MES-BOOL
-- [Warning]: redefining module MES-BOOL ,,,,,,_,,,,,,,,,_,,*.
-- defining module! MES-BOOL
-- [Warning]: redefining module MES-BOOL ._* done. done.
-- defining module! MES-QUEUE
-- [Warning]: redefining module MES-QUEUE ,,,,,,_,,,,,,,,,_,,*.
-- defining module! MES-QUEUE
-- [Warning]: redefining module MES-QUEUE ._* done. done.
-- defining module! ABP-DATA
-- [Warning]: redefining module ABP-DATA .,,,,,,_,,,,,,,,,_,,*.,,,,,,_,,,,,,,,,
-- _,,*........
-- defining module! ABP-DATA
-- [Warning]: redefining module ABP-DATA .........._._* done..* done.
-- defining module* UNRELIABLE-FIFO-CHANNEL
-- [Warning]: redefining module UNRELIABLE-FIFO-CHANNEL _.*.,,,,,,_,,*........_
-- ...*
-- Error: The index, 8, is too large
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by CAFEOBJ-EVAL-INPUT-PROC.
-- Broken at CAFEOBJ-EVAL-MODULE-PROC.  Type :H for Help.
-- CHAOS>>:q
-- 
-- CafeOBJ> q
-- [Leaving CafeOBJ]
-- bash$ exit
-- 
-- *******************FILE ABP1.TXT****************************
-- ===================================================================
-- Queue (parameterised)
-- ===================================================================
mod! QUEUE [ X :: TRIV ]
{
  [ Elt < NeQueue < Queue ]

  op nullQueue : -> Queue
  op get : NeQueue -> Elt
  op put : Elt Queue -> NeQueue
  op pop : NeQueue -> Queue

  var E : Elt
  var Q : NeQueue

  eq put(E, nullQueue) = E .
  eq get(E) = E .
  eq get(put(E, Q)) = get(Q) .
  eq pop(E) = nullQueue .
  eq pop(put(E, Q)) = put(E, pop(Q)) .
}

-- --------------------------------------------------------------------
-- test for module QUEUE (queue of natural numbers)
-- --------------------------------------------------------------------
mod! NAT-QUEUE
{
  protecting(QUEUE [ X <= view to NAT { sort Elt -> Nat } ])
}

mod* MESSAGE
{
  [ Mes ]
}

-- mod! 2TUPLE [ C1 :: TRIV, C2 :: TRIV ]
-- {
--   [ 2Tuple ]
-- 
--   op <<_;_>> : Elt.C1 Elt.C2 -> 2Tuple
--   op 1*_ : 2Tuple -> Elt.C1
--   op 2*_ : 2Tuple -> Elt.C2
-- 
--   var E1 : Elt.C1
--   var E2 : Elt.C2
-- 
--   eq 1* << E1 ; E2 >> = E1 .
--   eq 2* << E1 ; E2 >> = E2 .
-- }


mod! MES-BOOL
{
  protecting(2TUPLE [ C1 <= view to MESSAGE { sort Elt -> Mes },
                      C2 <= view to BOOL { sort Elt -> Bool } ]
             *{ sort 2Tuple -> MesBool })
}


mod! MES-QUEUE
{
  protecting(QUEUE [ X <= view to MESSAGE { sort Elt -> Mes } ]
                 *{ sort Queue -> MesQueue,
                    sort NeQueue -> NeMesQueue,
                    op nullQueue -> nullMesQueue })
}

mod! ABP-DATA
{
  protecting (MES-QUEUE)
  protecting (QUEUE [X <= MES-BOOL {sort Elt -> MesBool}]
	      * {sort Queue -> Fifo1Queue,
		 sort NeQueue -> NeFifo1Queue,
		 op nullQueue -> nullFifo1})
  protecting (QUEUE [X <= BOOL {sort Elt -> Bool}]
	      * {sort Queue -> Fifo2Queue,
		 sort NeQueue -> NeFifo2Queue,
		 op nullQueue -> nullFifo2})

  [ Config ]

  op (_,_;_;_,_;_) : MesQueue Bool Fifo1Queue MesQueue Bool Fifo2Queue ->
    Config
      
  vars Q-S Q-R : MesQueue
  -- vars Q-S Q-R : NeMesQueue
  var Q-F1 : Fifo1Queue
  var Q-F2 : Fifo2Queue
  vars Fl-S Fl-R : Bool
  var M : Mes

  ctrans (Q-S, Fl-S ; Q-F1 ; Q-R, Fl-R ; Q-F2) =>
    (Q-S, Fl-S ; put(<< get(Q-S) ; Fl-S >>, Q-F1) ; Q-R, Fl-R ; Q-F2)
  if
    get(Q-S) =/= nullMesQueue .
}

-- ----------------!!!
mod* UNRELIABLE-FIFO-CHANNEL [ X :: TRIV ]
{
  protecting (QUEUE[X])

  *[ UFifo ]*

  op nullUFifo : -> UFifo
  op put : Elt UFifo -> UFifo
  op pop : UFifo -> UFifo
  op get-queue : UFifo -> Queue

  var E : Elt
  var Q : UFifo

  eq get-queue(nullUFifo) = nullQueue .
  eq get-queue(put(E, Q)) = put(E, get-queue(Q)) .
  ceq get-queue(pop(Q)) = pop(get-queue(Q))
         if get-queue(Q) =/= nullQueue .
}

mod* FIFO1
{
  protecting(UNRELIABLE-FIFO-CHANNEL [ X <= view to MES-BOOL
                                       { sort Elt -> MesBool } ]
                         *{ hsort UFifo -> Fifo1,
                            op nullUFifo -> nullFifo1 })
}

mod* FIFO2
{
  protecting(UNRELIABLE-FIFO-CHANNEL [ X <= view to BOOL
                                       { sort Elt -> Bool } ]
                         *{ hsort UFifo -> Fifo2,
                            op nullUFifo -> nullFifo2 })
}

mod* SENDER-RECEIVER
{
  protecting(ABP-DATA)

  *[ SendRec ]*

  op srinit : -> SendRec
  op pop : SendRec -> SendRec
  op append : Mes SendRec -> SendRec
  op rev : SendRec -> SendRec
  op flag : SendRec -> Bool
  op buf : SendRec -> MesQueue

  var SR : SendRec
  var M : Mes

  eq flag(rev(SR)) = not flag(SR) .
  eq flag(pop(SR)) = flag(SR) .
  eq flag(append(M, SR)) = flag(SR) .
  eq buf(srinit) = nullMesQueue .
  ceq buf(pop(SR)) = pop(buf(SR)) if buf(SR) =/= nullMesQueue .
  eq buf(append(M, SR)) = put(M, buf(SR)) .
  eq buf(rev(SR)) = buf(SR) .
}

mod* SENDER
{
  extending(SENDER-RECEIVER *{ hsort SendRec -> Sender,
			       op srinit -> sender-init })

  eq flag(sender-init) = false .
}

mod* RECEIVER
{
  extending(SENDER-RECEIVER *{ hsort SendRec -> Receiver,
			       op srinit -> rec-init })

  eq flag(rec-init) = true .
}

mod* ABP1
{
  protecting (ABP-DATA)
  protecting(SENDER)
  protecting(FIFO1)
  protecting(RECEIVER)
  protecting(FIFO2)

  *[ Abp ]*

  op mes1 : Abp -> Abp            -- message from Sender to Fifo1
  op mes2 : Abp -> Abp            -- message from Fifo1 to Receiver
  op mes3 : Abp -> Abp            -- message from Receiver to Fifo2
  op mes4 : Abp -> Abp            -- message from Fifo2 to Sender
  op sender : Abp -> Sender       -- projection to Sender
  op fifo1 : Abp -> Fifo1         -- projection to Fifo1
  op receiver : Abp -> Receiver   -- projection to Receiver
  op fifo2 : Abp -> Fifo2         -- projection to Fifo2
  op abp-init : -> Abp            -- initial state of Abp

  var A : Abp
  var M : Mes

-- equations for sender
  eq sender(abp-init) = sender-init .
  eq sender(mes1(A)) = sender(A) .
  eq sender(mes2(A)) = sender(A) .
  eq sender(mes3(A)) = sender(A) .
  cq sender(mes4(A)) = pop(sender(A))
       if get-queue(fifo2(A)) =/= nullUMesQueue and
          flag(sender(A)) == get(get-queue(fifo2(A))) .
  cq sender(mes4(A)) = sender(A)
       if get-queue(fifo2(A)) =/= nullUMesQueue and
          flag(sender(A)) =/= get(get-queue(fifo2(A))) .
  cq sender(mes4(A)) = sender(A)
       if get-queue(fifo2(A)) == nullUMesQueue .

-- equations for fifo1
  eq fifo1(abp-init) = nullFifo1 .
  cq fifo1(mes1(A)) =
       put(<< get(buf(sender(A))) ; flag(sender(A)) >> , fifo1(A))
       if buf(sender(A)) =/= nullMesQueue .
  cq fifo1(mes1(A)) = fifo1(A)
       if buf(sender(A)) == nullMesQueue .
  cq fifo1(mes2(A)) = pop(fifo1(A))
       if get-queue(fifo1(A)) =/= nullUMesQueue .
  cq fifo1(mes2(A)) = fifo1(A)
       if get-queue(fifo1(A)) == nullUMesQueue .
  eq fifo1(mes3(A)) = fifo1(A) .
  eq fifo1(mes4(A)) = fifo1(A) .

-- equations for receiver
  eq receiver(abp-init) = rec-init .
  eq receiver(mes1(A)) = receiver(A) .
  cq receiver(mes2(A)) = append(1*(get(get-queue(fifo1(A)))), receiver(A))
       if buf(sender(A)) =/= nullMesQueue and
          2*(get(get-queue(fifo1(A)))) =/= flag(receiver(A)) .
  cq receiver(mes2(A)) = receiver(A)
       if buf(sender(A)) =/= nullMesQueue and
          2*(get(get-queue(fifo1(A)))) == flag(receiver(A)) .
  cq receiver(mes2(A)) = receiver(A)
       if buf(sender(A)) == nullMesQueue .
  eq receiver(mes3(A)) = receiver(A) .
  eq receiver(mes4(A)) = receiver(A) .

-- equations for fifo2
  eq fifo2(abp-init) = nullFifo2 .
  eq fifo2(mes1(A)) = fifo2(A) .
  eq fifo2(mes2(A)) = fifo2(A) .
  eq fifo2(mes3(A)) = put(flag(receiver(A)), fifo2(A)) .
  eq fifo2(mes4(A)) = pop(fifo2(A)) .
}

