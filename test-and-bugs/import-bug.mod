-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sat, 1 Nov 97 21:08:06 JST
-- Message-Id: <9711011208.AA03573@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  bug in importation
-- Content-Type: text
-- Content-Length: 1348

-- Dear Toshimi,

-- I woud like to specify commutative monoids by reusing the monoids but
-- of course using comm as attribute rather than equation (to avoid
-- non-termination).

mod* MON {
  [ Elt ]

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

mod* CMON {
  protecting(MON)

  op _;_ : Elt Elt -> Elt {comm}
}

-- But this doesnt work very well.

-- reduce in % : m ; n == n ; m
-- false : Bool
-- (0.010 sec for parse, 1 rewrites(0.030 sec), 17 match attempts)

-- despite the describe:

-- CMON> describe .
-- ======================================================================
--                            module CMON
--                           kind: theory
--                        type: user defined
--                created: 1997 Nov 1 Sat 3:53:55 GMT
-- ----------------------------------------------------------------------

--                         << submodules >>
--   protecting (MON)

--                 << sorts and subsort relations >>
--   * visible sorts :
--     Elt

--                    << operators and axioms >>

-- .............................(null).............................
--   * rank: -> Elt
-- .............................(_ ; _).............................
--   * rank: Elt Elt -> Elt
--     - attributes:  { comm r-assoc }
--     - axioms:
--       eq m:Elt ; null = m:Elt
--       eq null ; m:Elt = m:Elt

-- ---
-- Razvan
