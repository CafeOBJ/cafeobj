-- To: "sawada@sra.co.jp" <sawada@sra.co.jp>
-- Subject: a problem with reduction
-- Date: Mon, 09 Jun 97 19:37:57 -0500
-- From: Dorel Lucanu <dlucanu@infoiasi.ro>
-- X-Mailer: E-Mail Connection v2.5.02
-- Content-Type: text
-- Content-Length: 6684

-- -- [ From: Dorel Lucanu * EMC.Ver #2.5.02 ] --

-- Dear Sawada,

-- Below you find  two dialogues with CafeOBJ which I don't understand. The two
-- dialogues refer similar input files but with different behaviours of CfaeOBJ
-- . In fact, in the second dialogoue I just changed the line

--   cq val(next(C)) = val(C) + 1 if not(val(C) == p n) .

-- by the line

--   cq val(next(C)) = val(C) + 1 if  val(C) =/= p n .

-- in the module COUNTER. In my opinion, in both cases the the term "val(next(c
-- ))'' should have been reduce to 51. It seems that the problems are caused by
-- these two equations, because I changed the equation 

--   eq k = 50 .

-- by
  
--   eq k = 99

-- in the file LEMA3 and the term "val(next(c))" was reduced correctly to 0.
-- I would be happy to know if it is a mistake from my part or a bug of the
-- system.

-- Yours sincerely,

-- Dorel Lucanu.




-- *************************Dialogoue with CafeOBJ*****************
-- ./cafeobj counter
-- -- loading standard prelude
-- [Error]: no such file: std

-- ** returning to top level

--                   -- CafeOBJ system Version 1.3.b3 --
--                    built: 1997 Jun 3 Tue 11:14:06 GMT
--                           prelude file: NONE
--                                   ***
--                       1997 Jun 9 Mon 15:28:48 GMT
--                             Type ? for help
--                                   ---
--                       uses GCL (GNU Common Lisp)
--                Licensed under GNU Public Library License
--                  Contains Enhancements by W. Schelter
-- -- processing input : ./counter.mod
-- -- defining module NUMBER_.._* done.
-- -- defining module TEN_.._.* done.
-- -- defining module HUNDRED_.._.* done.
-- -- defining module COUNTER__.*......._....* done.
-- -- defining module COUNTER1,,,,,,_,,,,,,,,,,,_,,*,,,,,_,,*._* done.
-- -- defining module COUNTER2,,,,,,,,,_,,*,,,,,_,,*._* done.
-- -- defining module DCOUNTER..........._...........* done.
-- -- defining module COUNTERH,,,,,,_,,,,,,,,,_,,*._* done.
-- -- defining module TEST..
-- [Warning]: behavioural operator "_R_" has imported hidden sort Counter.
--            COUNTER(X <= HUNDRED) * { ... } in its arity.
-- [Warning]: behavioural operator "_R_" has imported hidden sort DCounter in
-- its arity...._.* done.

-- CafeOBJ> in lema3
-- -- processing input : ./lema3.mod_
-- **> Lemma 3 .
-- **> Presumption .
-- **> Conclusion

-- %TEST> red not(val(c) == p n) .
-- *
-- -- reduce in % : not val(c) == p n
-- true : Bool
-- (0.010 sec for parse, 6 rewrites(0.010 sec), 7 match attempts)

-- %TEST> red val(next(c)) .
-- -- reduce in % : val(next(c))
-- Error: The index, 8, is too large
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by CAFEOBJ-EVAL-REDUCE-PROC.
-- Broken at PERFORM-REDUCTION.  Type :H for Help.
-- CHAOS>>:q

-- %TEST> q
-- [Leaving CafeOBJ]
-- odin (dlucanu):~/cafeobj/cafeobj-1.3.b3/xbin>./cafeobj counter
-- -- loading standard prelude
-- [Error]: no such file: std

-- ** returning to top level

--                   -- CafeOBJ system Version 1.3.b3 --
--                    built: 1997 Jun 3 Tue 11:14:06 GMT
--                           prelude file: NONE
--                                   ***
--                       1997 Jun 9 Mon 15:30:14 GMT
--                             Type ? for help
--                                   ---
--                       uses GCL (GNU Common Lisp)
--                Licensed under GNU Public Library License
--                  Contains Enhancements by W. Schelter
-- -- processing input : ./counter.mod
-- -- defining module NUMBER_.._* done.
-- -- defining module TEN_.._.* done.
-- -- defining module HUNDRED_.._.* done.
-- -- defining module COUNTER__.*......._....* done.
-- -- defining module COUNTER1,,,,,,_,,,,,,,,,,,_,,*,,,,,_,,*._* done.
-- -- defining module COUNTER2,,,,,,,,,_,,*,,,,,_,,*._* done.
-- -- defining module DCOUNTER..........._...........* done.
-- -- defining module COUNTERH,,,,,,_,,,,,,,,,_,,*._* done.
-- -- defining module TEST..
-- [Warning]: behavioural operator "_R_" has imported hidden sort Counter.
--            COUNTER(X <= HUNDRED) * { ... } in its arity.
-- [Warning]: behavioural operator "_R_" has imported hidden sort DCounter in
-- its arity...._.* done.

-- CafeOBJ> in lema3
-- -- processing input : ./lema3.mod_
-- **> Lemma 3 .
-- **> Presumption .
-- **> Conclusion

-- %TEST> red val(c) =/= p n .
-- *
-- -- reduce in % : val(c) =/= p n
-- true : Bool
-- (0.010 sec for parse, 5 rewrites(0.000 sec), 5 match attempts)

-- %TEST> red val(next(c)) .
-- -- reduce in % : val(next(c))Segmentation Fault (core dumped)
-- odin (dlucanu):~/cafeobj/cafeobj-1.3.b3/xbin>exit


-- ****************File COUNTER.MOD**************
mod NUMBER 
{ 
  using (NAT)
  -- op n : -> Nat
  op n : -> NzNat
}

mod TEN 
{ 
  using (NAT)
  -- op n : -> Nat
  op n : -> NzNat
  eq n = 10 .
}

mod HUNDRED 
{ 
  using (NAT)
  -- op n : -> Nat
  op n : -> NzNat
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

-- ****************File LEMA3.MOD**************

open TEST

op c : -> Counter.COUNTERH .

op d : -> DCounter .

ops k k1 k2 : -> Nat .

eq val(second(d)) = k1 .

eq val(first(d)) = k2 .

eq k1 * 10 + k2 = k .

eq val(c) = k .


**> Lemma 3 .

**> Presumption .

eq k = 50 .

**> Conclusion

-- red next(c) R dnext(d) .
