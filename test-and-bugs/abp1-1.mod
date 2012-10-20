-- ***********************FILE ABP1_1.TXT*************************

-- ===================================================================
-- Queue (parameterised)
-- ===================================================================
mod! QUEUE (X :: TRIV)
{
  signature {
    [ Elt < NeQueue < Queue ]
    op nullQueue : -> Queue
    op get : NeQueue -> Elt
    op put : Elt Queue -> NeQueue
    op pop : NeQueue -> Queue
  }

  axioms {
    var E : Elt
    var Q : NeQueue
    -- ----------------------------------
    eq put(E, nullQueue) = E .
    eq get(E) = E .
    eq get(put(E, Q)) = get(Q) .
    eq pop(E) = nullQueue .
    eq pop(put(E, Q)) = put(E, pop(Q)) .
  }
}

-- --------------------------------------------------------------------
-- test for module QUEUE (queue of natural numbers)
-- --------------------------------------------------------------------
mod! NAT-QUEUE
     principal-sort Queue
{
  -- now we have principal-sort, and Elt of TRIV and Nat of NAT is
  -- declared as principal, thus instead of
  -- protecting(QUEUE [ X <= view to NAT { sort Elt -> Nat } ])
  -- we can write it as
  protecting (QUEUE[NAT])	-- uses old syntax of instantiation.
}

mod* MESSAGE
     principal-sort Mes
{
  [ Mes ]
}

-- mod! 2TUPLE [ C1 :: TRIV, C2 :: TRIV ]
-- {
--   [ 2Tuple ]
	    
--   op <<_;_>> : Elt.C1 Elt.C2 -> 2Tuple
--   op 1*_ : 2Tuple -> Elt.C1
--   op 2*_ : 2Tuple -> Elt.C2
	    
--   var E1 : Elt.C1
--   var E2 : Elt.C2

--   eq 1* << E1 ; E2 >> = E1 .
--   eq 2* << E1 ; E2 >> = E2 .
-- }


mod! MES-BOOL
     principal-sort MesBool
{
  -- protecting(2TUPLE [ C1 <= view to MESSAGE { sort Elt -> Mes }
  -- 		      C2 <= view to BOOL { sort Elt -> Bool } ]
  --	     * { sort 2Tuple -> MesBool })
  protecting(2TUPLE(C1 <= MESSAGE, C2 <= BOOL)
	       * { sort 2Tuple -> MesBool })
}

mod! MES-QUEUE
{
  protecting(QUEUE (X <= MESSAGE) *{ sort Queue -> MesQueue,
				     sort NeQueue -> NeMesQueue,
				     op nullQueue -> nullMesQueue })
}

mod! ABP-DATA
{
  imports {
    protecting (MES-QUEUE)
    protecting (QUEUE [X <= MES-BOOL] * { sort Queue -> Fifo1Queue,
					  sort NeQueue -> NeFifo1Queue,
					  op nullQueue -> nullFifo1})
    protecting (QUEUE [X <= BOOL] * { sort Queue -> Fifo2Queue,
				      sort NeQueue -> NeFifo2Queue,
				      op nullQueue -> nullFifo2})
  }

  signature {
    [ Config ]

    op (_,_;_;_,_;_) : MesQueue Bool Fifo1Queue MesQueue Bool Fifo2Queue
      -> Config
      }
  axioms {
    vars Q-S Q-R : MesQueue
    var Q-F1 : Fifo1Queue
    var Q-F2 : Fifo2Queue
    vars Fl-S Fl-R : Bool
    var M : Mes

    ctrans (Q-S, Fl-S ; Q-F1 ; Q-R, Fl-R ; Q-F2) =>
      (Q-S, Fl-S ; put(<< get(Q-S) ; Fl-S >>, Q-F1) ; Q-R, Fl-R ; Q-F2)
	if get(Q-S) =/= nullMesQueue .
  }
}


mod* UNRELIABLE-FIFO-CHANNEL [ X :: TRIV ]
{
  protecting (QUEUE[X])
    
  signature {
    *[ UFifo ]*

    op nullUFifo : -> UFifo
    bop put : Elt UFifo -> UFifo
    bop pop : UFifo -> UFifo
    bop get-queue : UFifo -> Queue
  }

  axioms {
    var E : Elt
    var Q : UFifo

    eq get-queue(nullUFifo) = nullQueue .
    eq get-queue(put(E, Q)) = put(E, get-queue(Q)) .
    ceq get-queue(pop(Q)) = pop(get-queue(Q))
      if get-queue(Q) =/= nullQueue .
  }
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
  bop pop : SendRec -> SendRec
  bop append : Mes SendRec -> SendRec
  bop rev : SendRec -> SendRec
  bop flag : SendRec -> Bool
  bop buf : SendRec -> MesQueue

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
  using(SENDER-RECEIVER *{ hsort SendRec -> Sender,
                           op srinit -> sender-init })
    
  eq flag(sender-init) = false .
}

mod* RECEIVER
{
  using(SENDER-RECEIVER *{ hsort SendRec -> Receiver,
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
    if get-queue(fifo2(A)) =/= nullMesQueue and
      flag(sender(A)) == get(get-queue(fifo2(A))) .
  cq sender(mes4(A)) = sender(A)
    if get-queue(fifo2(A)) =/= nullMesQueue and
      flag(sender(A)) =/= get(get-queue(fifo2(A))) .
  cq sender(mes4(A)) = sender(A)
    if get-queue(fifo2(A)) == nullMesQueue .

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

eof
