-- Date: Tue, 27 May 1997 01:57:24 +0100
-- From: "Ataru T. Nakagawa" <nakagawa@sra.co.jp>
-- Message-Id: <199705270057.BAA08215@sran419.sra.co.jp>
-- To: diacon@stoilow.imar.ro
-- CC: h-ishika@jaist.ac.jp, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, n-ume@jaist.ac.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp, sawada@sra.co.jp, nakagawa@sra.co.jp
-- In-reply-to: Diaconescu Razvan's message of Sun, 25 May 1997 09:10:32 +0300 <9705250610.AA02371@stoilow.imar.ro>
-- Subject: module expressions vs. theory morphisms diagrams
-- Content-Type: text
-- Content-Length: 5186
-- 
--
-- Cher Razvan-san,
-- 
-- I wonder the following example is "good", but let me proceed.
-- As building blocks, we have

--
module* B-STACK (X :: TRIV) {
  [ Stack ]
  op push : Elt Stack -> Stack
}

module! TRAY (Y :: B-STACK) {
  [ Tray ]
  op tray : Stack Stack -> Tray
  ops in-tray out-tray : Tray -> Stack
  op in : Elt Tray -> Tray 
  var E : Elt
  vars S S' : Stack
  eq in(E, tray(S,S')) = tray(push(E,S),S') .
  trans tray(push(E,S),S') => tray(S, push(E, S')) .
  eq in-tray(tray(S,S')) = S .
  eq out-tray(tray(S,S')) = S' .
}

-- not the Lord, but linear orders
module* LORD {
  [ Elt ]
  op _<_ : Elt Elt -> Bool
  vars E E' E'' : Elt
  eq E < E = false .
  eq E < E' = E' < E'' and E'' < E' .
  eq E < E' or E' < E or E == E' = true .
}

view V from TRIV to LORD {
  sort Elt -> Elt
}

module! P-QUEUE (Z :: LORD) {
  [ Queue ]
  op e : -> Queue
  op enq : Elt Queue -> Queue
  op first : Queue -> Elt
  op deq : Queue -> Queue
  var E : Elt
  var Q : Queue
  cq first(enq(E, Q)) = E if first(Q) < E .
  cq first(enq(E, Q)) = first(Q) if not (first(Q) < E) .
  eq deq(e) = e .
  cq deq(enq(E, Q)) = Q if first(Q) < E .
  cq deq(enq(E, Q)) = enq(E, deq(Q)) if not (first(Q) < E) .
}

view W from B-STACK to P-QUEUE {
  sort Elt -> Elt
  sort Stack -> Queue
  op push -> enq
}
--

-- We then get the desired diagram (which, in this case, commutes).
-- In instantiation, we write

--
module QUEUE-TRAY {
  protecting (TRAY(Y <= W))
}
--

-- Here only a single view and a parameter name appears.
-- And in this case, the current system creates a ground module
-- (so there is no way to instantiate this module further.
-- As I said earlier, the module should remain parameterised.)
-- Note that, in W, a map Elt -> Elt is given. This map is exactly as
-- given by V.

-- For the sake of variety, I also give a non-commutative example below
-- (this example is somewhat artificial, though).

--
module* TWO {
  [ Elt1 < Elt2 ]
}

module* B-MIX-STACK (X :: TWO) {
  [ Elt1 Elt2 < Elt, Stack ]
  op push : Elt Stack -> Stack
}

module! TRAY' (Y :: B-MIX-STACK) {
  [ Tray ]
  op tray : Stack Stack -> Tray
  ops in-tray out-tray : Tray -> Stack
  op in : Elt Tray -> Tray 
  var E : Elt
  vars S S' : Stack
  eq in(E, tray(S,S')) = tray(push(E,S),S') .
  trans tray(push(E,S),S') => tray(S, push(E, S')) .
  eq in-tray(tray(S,S')) = S .
  eq out-tray(tray(S,S')) = S' .
}

-- not words, but well-orders
module* WORD {
  [ Bot < Elt ]
  op 0 : -> Bot
  op _<_ : Elt Elt -> Bool
  vars E E' E'' : Elt
  cq 0 < E = true if E =/= 0 .
  eq E < E = false .
  eq E < E' = E' < E'' and E'' < E' .
  eq E < E' or E' < E or E == E' = true .
}

view V' from TWO to WORD {
  sort Elt1 -> Bot
  sort Elt2 -> Elt
}

module! P-QUEUE' (Z :: WORD) {
  [ Queue ]
  op e : -> Queue
  op enq : Elt Queue -> Queue
  op first : Queue -> Elt
  op deq : Queue -> Queue
  var E : Elt
  var Q : Queue
  eq first(e) = 0 .
  cq first(enq(E, Q)) = E if first(Q) < E .
  cq first(enq(E, Q)) = first(Q) if not (first(Q) < E) .
  eq deq(e) = e .
  cq deq(enq(E, Q)) = Q if first(Q) < E .
  cq deq(enq(E, Q)) = enq(E, deq(Q)) if not (first(Q) < E) .
}

view W' from B-MIX-STACK to P-QUEUE' {
  sort Elt1 -> Elt
  sort Elt2 -> Elt
  sort Elt -> Elt
  sort Stack -> Queue
  op push -> enq
}
--

-- This example is non-commutative, since Elt1 is mapped to Bot
-- or Elt, depending on whether we go along down-right or right-down.
-- In this case, the system refuses to accept the expression below
-- (it causes an error).

--
module QUEUE-TRAY' {
  protecting (TRAY'(Y <= W'))
}
--

-- Going back to the first example, it is also possible to write
--
module M {
  protecting (TRAY(Y <= view to P-QUEUE(Z <= view to LORD {})
		   { sort Elt -> Elt
		     sort Stack -> Queue
		     op push -> enq }))
}
--

-- This expression creates a ground module, as expected. It seems
-- this expression is as near as we can get to depict the diagram.
-- The deficiency is that the view W cannot be named.
-- It appears implicitly, as a view on the fly.
-- Well, well.
-- I am thinking of two ways to make the things more explicit. One is to
-- allow view importation, as suggested by Razvan-san in March meeting.
-- To use a tentative syntax, we modify W above as

eof

view W from B-STACK to P-QUEUE {
  extending V
  sort Stack -> Queue
  op push -> enq
}

-- In this modification, the mod.exp. is as before, i.e.

--  protecting (TRAT(Y <= W))

-- but the situation is psychologically more satisfactory, since V does
-- appear in the definition of W.

-- The second approach is to "parameterise" views. Again using a tentative
-- syntax, we have something like

view W (M :: X -> Z) from B-STACK to P-QUEUE {
  sort Stack -> Queue
  op push -> enq
}

-- and in instantiation, we write

module QUEUE-TRAY {
  protecting (TRAT(Y <= W(M <= V)))
}

-- These changes may lead to dramatic syntactic extensions, by creating a
-- notion of view calculus. That is all for now from me...
-- 
-- Best Regards,
-- ATN
