-- From: Michihiro Matumoto <mitihiro@jaist.ac.jp>
-- Date: Wed, 29 Oct 97 14:28:56 JST
-- Message-Id: <9710290528.AA15271@is27e0s04.jaist.ac.jp>
-- To: diacon@jaist.ac.jp
-- Cc: diacon@stoilow.imar.ro, ishisone@sra.co.jp
-- Cc: kokichi@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp
-- Cc: s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Cc: mitihiro@jaist.ac.jp
-- In-Reply-To: <9710280821.AA02504@is27e0s07.jaist.ac.jp> (message from Razvan Diaconescu on Tue, 28 Oct 97 17:21:02 JST)
-- Subject: Re: a couple of small beh specification corrections
-- Content-Type: text
-- Content-Length: 7155

-- Dear All,

-- > --------------------------------------
-- > 1. The message about whether the checking for =*= is succesful or it
-- > fails should be FOR THE MODULE rather than for individual
-- > sorts. Conceptually the congruence for one sort doesnt make sense, the
-- > concept of congruence is linked to the whole signature involved. For
-- > example, if for at least one sort the checking of =*= fails one cannot
-- > use it for the other sorts either. 
-- > 
-- > So, when CafeOBJ loads a beh module <module-name> then the message
-- > shoud be like: 
-- > 
-- > * system failed to prove =*= is a congruence of <module-name>.
-- > 
-- > or
-- > 
-- > * system already proved =*= is a congruence of <module-name>.
-- > ---------------------------------------

-- I agree. 

-- Also I want the swith to select whether "default check" is executed.
-- Because, We can know whether "default check" succeed without
-- the execution of "default check". For example, by using Test Set
-- Coinduction.

-- The case I want to stop "default check" is as follows.
-- For this proof score, most of the time is spent by "default check"
-- which certainly fail.

--   To sawada-san,
--      In my memory -- I'm sorry that there is no CafeOBJ ver1.3 
--    here now --, on CafeOBJ Ver1.3 following code succeeds, 
--    but on CafeOBJ ver1.4b3 it fails. I think it may be bug.
--    vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
--      -- (4) len rq dq = 0, len lq dq = 0
--      open .
--      op e : -> Elt .
--      op dq : -> DoubleQueue .
--      eq len rq dq = 0 .
--      eq len lq dq = 0 .

--      red rq pop put(e, dq) =b= rq dq .
--    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv

-- set auto context on .
-- unprotect INT
-- unprotect NAT

mod! INT' {

  [ Nat < Int ]

  op 0 : -> Nat
  op s_ : Nat -> Nat
  op s_ : Int -> Int
  op p_ : Int -> Int

  op _+_ : Int Int -> Int
  op -_ : Int -> Int

  vars I J : Int
  eq s p I = I .
  eq p s I = I .

  eq I + 0 = I .
  eq 0 + I = I .
  eq I + s J = s(I + J) .
  eq s I + J = s(I + J) .
  eq I + p J = p(I + J) .
  eq p I + J = p(I + J) .
  eq - 0 = 0 .
  eq - (s I) = p (- I) .
  eq - (p I) = s (- I) .
}

mod* ETRIV {
  [ Elt < ExtElt ]

  op err : -> ExtElt
}

mod QUEUE [ X :: ETRIV ] {
  pr(INT')

  *[ Queue ]*
  bop get_ : Queue -> Elt
  bop len_ : Queue -> Nat
  bop put : Elt Queue -> Queue
  bop pop_ : Queue -> Queue

  var E : Elt
  var Q : Queue

  ceq get Q = err
      if len Q == 0 .
  ceq get put(E, Q) = get Q
      if len Q =/= 0 .
  ceq get put(E, Q) = E
      if len Q == 0 .
  eq len put(E, Q) = s len Q .
  ceq len pop Q = p len Q
      if len Q =/= 0 .
  ceq len pop Q = 0
      if len Q == 0 .
  bceq pop Q = Q
       if len Q == 0 .
  bceq pop put(E, Q) = put(E, pop Q)
       if len Q =/= 0 .
  bceq pop put(E, Q) = Q
       if len Q == 0 .
}

mod EXTQUEUE [ X :: ETRIV ] {
  pr(INT')
  -- pr(QUEUE [ X ])
  ex(QUEUE [ X ])

  *[ ExtQueue < Queue ]*
  bop put : ExtElt ExtQueue -> ExtQueue
  bop pop_ : ExtQueue -> ExtQueue

  var EQ : ExtQueue
  eq get put(err, EQ) = err .
  eq len put(err, EQ) = len EQ .
  beq pop put(err, EQ) = put(err, pop EQ) .
}

mod DOUBLEQUEUE [ X :: ETRIV ] {
  pr(INT')
  pr(EXTQUEUE [ X ])

  *[ DoubleQueue ]*

  bop get_ : DoubleQueue -> Elt
  bop len_ : DoubleQueue -> Nat

  bop put : Elt DoubleQueue -> DoubleQueue
  bop pop_ : DoubleQueue -> DoubleQueue
  bop move_ : DoubleQueue -> DoubleQueue

  bop lq_ : DoubleQueue -> Queue
  bop rq_ : DoubleQueue -> ExtQueue

  var E : Elt
  var Q : Queue
  var DQ : DoubleQueue

  ceq get DQ = get rq DQ
      if len rq DQ =/= 0 .

  eq len DQ = len lq DQ + len rq DQ .

  beq rq put(E, DQ) = rq DQ .
  bceq rq pop DQ = pop rq DQ
       if len rq DQ =/= 0 .
  beq rq move DQ = put(get lq DQ, rq DQ) .

  beq lq put(E, DQ) = put(E, lq DQ) .
  bceq lq pop DQ = lq DQ
       if len rq DQ =/= 0 .
  beq lq move DQ = pop lq DQ .

-- Waiting until the state is changed
--  ceq get DQ = get move DQ if len rq DQ == 0 .
  ceq get DQ = get rq move DQ
      if len rq DQ == 0 .
--  bceq pop DQ = pop move DQ  if len rq DQ == 0 .
  bceq rq pop DQ = pop rq move DQ
       if len rq DQ == 0 .
  bceq lq pop DQ = lq move DQ
       if len rq DQ == 0 .
}

select DOUBLEQUEUE .

-- (1) len rq dq =/= 0, len lq dq =/= 0
open .
op e : -> Elt .
op dq : -> DoubleQueue .

red get put(e, dq) == get dq .
red len put(e, dq) == s len dq .
red len pop dq == p len dq .
--  pop put(e, dq) =b= put(e, pop dq)
red rq pop put(e, dq) =b= rq put(e, pop dq) .
red lq pop put(e, dq) =b= lq put(e, pop dq) .
close

-- (2) len rq dq = 0, len lq dq =/= 0
open .
op e : -> Elt .
op dq : -> DoubleQueue .
eq len rq dq = 0 .

red get put(e, dq) == get dq .
red len put(e, dq) == s len dq .
red len pop dq == p len dq .
--  pop put(e, dq) =b= put(e, pop dq)
red rq pop put(e, dq) =b= rq put(e, pop dq) .
red lq pop put(e, dq) =b= lq put(e, pop dq) .
close

-- (3) len rq dq =/= 0, len lq dq = 0
open .
op e : -> Elt .
op dq : -> DoubleQueue .
eq len lq dq = 0 .

red get put(e, dq) == get dq .
red len put(e, dq) == s len dq .
red len pop dq == p len dq .
--  pop put(e, dq) =b= put(e, pop dq)
red rq pop put(e, dq) =b= rq put(e, pop dq) .
red lq pop put(e, dq) =b= lq put(e, pop dq) .
close

**> (4) len rq dq = 0, len lq dq = 0
open .
op e : -> Elt .
op dq : -> DoubleQueue .
eq len rq dq = 0 .
eq len lq dq = 0 .

red get dq == err .
red get put(e, dq) == e .
red len put(e, dq) == s len dq .
red len pop dq == 0 .
--  pop dq =b= dq
--   rq pop dq =b= rq dq => (5)
red lq pop dq =b= lq dq .
--  pop put(e, dq) =b= dq .
red rq pop put(e, dq) =b= rq dq .
red lq pop put(e, dq) =b= lq dq .
close

-- (5) rq pop dq =b= rq dq (len dq = 0)
-- lemma : pop*(put(err, EQ), N) =b= put(err, pop*(EQ, N))
open .
op n : -> Nat .
op exq : -> ExtQueue .

bop pop* : Queue Nat -> Queue .
bop pop* : ExtQueue Nat -> ExtQueue .
var Q : Queue .
var N : Nat .
var EQ : ExtQueue .
eq pop*(Q, 0) = Q .
eq pop*(Q, s N) = pop*(pop Q, N) .

--  base case (n = 0)
red pop*(put(err, exq), 0) =b= put(err, pop*(exq, 0)) .
--  induction step
beq pop*(put(err, EQ), n) = put(err, pop*(EQ, n)) .
red pop*(put(err, exq), s n) =b= put(err, pop*(exq, s n)) .
close

-- lemma : len pop*(rq dq, n) = 0
open .
op e : -> Elt .
op n : -> Nat .
op dq : -> DoubleQueue .
eq len rq dq = 0 .
eq len lq dq = 0 .

op pop* : Queue Nat -> Queue .
var Q : Queue .
var N : Nat .
eq pop*(Q, 0) = Q .
eq pop*(Q, s N) = pop pop*(Q, N) .

--  base case (n = 0)
red len pop*(rq dq, 0) == 0 .
--  induction step
eq len pop*(rq dq, n) = 0 .
red len pop*(rq dq, s n) == 0 .
close

-- proof score of "rq pop dq =b= rq dq"
open .
op e : -> Elt .
op n : -> Nat .
op dq : -> DoubleQueue .
eq len rq dq = 0 .
eq len lq dq = 0 .

bop pop* : Queue Nat -> Queue .
bop pop* : ExtQueue Nat -> ExtQueue .
var Q : Queue .
var N : Nat .
eq pop*(Q, 0) = Q .
eq pop*(Q, s N) = pop*(pop Q, N) .
var EQ : ExtQueue .
-- lemma
beq pop*(put(err, EQ), N) = put(err, pop*(EQ, N)) .
eq len pop*(rq dq, n) = 0 .

red get rq pop dq == get rq dq .
red get pop pop*(rq pop dq, n) == get pop pop*(rq dq, n) .
red len rq pop dq == len rq dq .
close

-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- Yours sincerely,
-- Michihiro Matsumoto (mitihiro@jaist.ac.jp)
