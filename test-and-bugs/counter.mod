-- To: "sawada@sra.co.jp" <sawada@sra.co.jp>
-- Subject: a problem with reduction
-- Date: Mon, 09 Jun 97 19:37:57 -0500
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- X-Mailer: E-Mail Connection v2.5.02
-- Content-Type: text
-- Content-Length: 6684

-- [ From: Dorel Lucanu * EMC.Ver #2.5.02 ] --

-- Dear Sawada,

-- Below you find  two dialogues with CafeOBJ which I don't understand. The two
-- dialogues refer similar input files but with different behaviours of CfaeOBJ
-- . In fact, in the second dialogoue I just changed the line
--
--   cq val(next(C)) = val(C) + 1 if not(val(C) == p n) .
-- 
-- by the line
-- 
--   cq val(next(C)) = val(C) + 1 if  val(C) =/= p n .
-- 
-- in the module COUNTER. In my opinion, in both cases the the term "val(next(c
-- ))'' should have been reduce to 51. It seems that the problems are caused by
-- these two equations, because I changed the equation 
-- 
--   eq k = 50 .
-- 
-- by
--   
--   eq k = 99

-- in the file LEMA3 and the term "val(next(c))" was reduced correctly to 0.
-- I would be happy to know if it is a mistake from my part or a bug of the
-- system.
-- 
-- Yours sincerely,
-- 
-- Dorel Lucanu.
--

mod NUMBER 
{ 
  extending (NAT)  -- using (NAT)
  op n : -> Nat
}

mod TEN 
{ 
  extending (NAT)   -- using (NAT)
  op n : -> Nat
  eq n = 10 .
}

mod HUNDRED 
{ 
  extending (NAT)  -- using (NAT)
  op n : -> Nat
  eq n = 100 .
}

mod COUNTER [ X :: NUMBER ]
{
  *[ Counter ]*
  op val : Counter -> Nat
  op next : Counter -> Counter
  op clear : Counter -> Counter
  op init-Counter : -> Counter

  var C : Counter
  
  cq val(next(C)) = val(C) + 1 if not(val(C) == p n) .
  cq val(next(C)) = 0 if val(C) == p n .
  eq val(init-Counter) = 0 .
  eq val(clear(C)) = 0 .
}

mod COUNTER1
{
  protecting (COUNTER[TEN] *{op   n -> n1,
                             op init-Counter -> init-Counter1})
}
mod COUNTER2
{
  protecting (COUNTER[TEN] *{op   n -> n2,
                             op init-Counter -> init-Counter2})
}
mod DCOUNTER
{
  *[ DCounter ]*
  protecting (COUNTER1)
  protecting (COUNTER2)
  op first : DCounter -> Counter.COUNTER1
  op second : DCounter -> Counter.COUNTER2
  op dval : DCounter -> Nat
  op dnext : DCounter -> DCounter
  op dclear : DCounter -> DCounter
  op round : DCounter -> DCounter
  op init-DCounter : -> DCounter

  var D : DCounter
  
  eq dval(D) = n1 * val(second(D)) + val(first(D)) .
  eq dval(dclear(D)) = 0 .

  cq second(dnext(D)) = second(D)  if val(first(D)) =/= p n1 .
  cq second(dnext(D)) = next(second(D))  if val(first(D)) == p n1 .
  eq second(dclear(D)) = clear(second(D)) .
  eq second(round(D)) = second(D) .
  eq second(init-DCounter) = init-Counter2 .
  
  eq first(dnext(D)) = next(first(D))  .
  eq first(dclear(D)) = clear(first(D)) .
  eq first(round(D)) = clear(first(D)) .
  eq first(init-DCounter) = init-Counter1 .
}

mod COUNTERH
{
  protecting (COUNTER(X <= HUNDRED) * {op init-Counter -> init-CounterH})
}

mod TEST
{
  protecting (DCOUNTER)
  protecting (COUNTERH)
  op _ R _ : Counter.COUNTERH DCounter -> Bool
  var C : Counter.COUNTERH
  var D : DCounter
  cq C R D = true if val(C) == dval(D) .
}
