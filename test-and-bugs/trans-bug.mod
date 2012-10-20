-- Date: Sun, 9 Nov 1997 17:21:04 +0200
-- From: Diaconescu Razvan <diacon@stoilow.imar.ro>
-- Message-Id: <9711091521.AA05430@stoilow.imar.ro>
-- To: sawada@sra.co.jp
-- Subject:  bug in execution of ==>
-- Content-Type: text
-- Content-Length: 542

-- Toshimi,

-- This might be a bug in the evaluation of ==>:

mod! STRG(X :: TRIV) {
  [ Elt < Strg ]

  op _._ : Strg Strg -> Strg { assoc }
  op null :  -> Strg 

  eq null . S:Strg = S .
  eq S:Strg . null = S .
}

mod! SORTING-STRG {
  protecting(STRG(NAT))

  ctrans N:Nat . N':Nat => N' . N 
     if (N' < N) .
}

red in SORTING-STRG : (4 . 3 . 2) ==> (3 . 4 . 2) .

-- reduce in SORTING-STRG : 4 . 3 . 2 ==> 3 . 4 . 2
-- 4 . 3 . 2 ==> 3 . 4 . 2 : Bool
-- (0.020 sec for parse, 38 rewrites(1.330 sec), 280 match attempts)

-- I think it should give *true*.

--
-- Razvan
