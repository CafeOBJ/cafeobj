-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Mon, 25 May 98 16:15:20 JST
-- Message-Id: <9805250715.AA02911@is27e0s07.jaist.ac.jp>
-- To: ishisone@sra.co.jp, sawada@sra.co.jp
-- Subject:  some bug when executing with brute
-- Content-Type: text
-- Content-Length: 2279

-- I found a bug when executing some sorting with brute. I think it has
-- something to do with instantiation and translation to brute rather
-- than brute itself.

-- generic strings
mod! STRG (X :: TRIV) {
  [ Elt < Strg ]

  op nil :  -> Elt 
  op __ : Strg Strg -> Strg {assoc idr: nil} 
}

-- the theory of partially ordered sets
mod* POSET {
  [ Elt ]

  op _<=_ : Elt Elt -> Bool 

  vars E1 E2 E3 : Elt

  eq E1 <= E1 = true .
  cq E1 = E2      if (E1 <= E2) and (E2 <= E1) .
  cq (E1 <= E3) = true      if (E1 <= E2) and (E2 <= E3) .
}

-- generic sorting algorithm
mod! SORTING-STRG(Y :: POSET) {
  protecting(STRG(Y))
  
  ctrans N:Elt N':Elt => N' N  if (N' <= N) and (N =/= N') .
}

select SORTING-STRG(NAT)
exec (4 3 5 3 1) .
-- fast execution by brute engine
-- set tram path brute .
-- eof

-- tram exec (40  39  38  37  36  35  34  33  32  31  30  29  28  27  26  25  24  23  22  21  20  19  18  17  16  15  14  13  12  11  10  9  8  7  6  5  4  3  2  1) .
exec (40  39  38  37  36  35  34  33  32  31  30  29  28  27  26  25  24  23  22  21  20  19  18  17  16  15  14  13  12  11  10  9  8  7  6  5  4  3  2  1) .
-- execute in SORTING-STRG(Y <= NAT) : 4 3 5 3 1
-- 1 3 3 4 5 : Strg
-- (0.010 sec for parse, 61 rewrites(0.110 sec), 107 matches)
-- execute in SORTING-STRG(Y <= NAT) : 40 39 38 37 36 35 34 33 32 
--    31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 
--    10 9 8 7 6 5 4 3 2 1
eof

[Error] error occured while reduction in comiled code...
error operator |_=\(_\)=>_| has invalid arity |?Nat*+Strg..trs#9.|.
error operator |_=\(_\)=>_| has invalid arity |?Nat*+Strg..trs#8.|.
warning attribute conflict for operator _+_ (15 != 3).
warning attribute conflict for operator |__?Nat*+Strg..trs#6.| (0 != 13).
warning attribute conflict for operator _*_ (0 != 15).
warning attribute conflict for operator |d/2| (0 != 2).
warning attribute conflict for operator _+_ (0 != 15).
warning attribute conflict for operator |_and_| (0 != 15).
warning strategy conflict for operator |_and-also_|.
warning attribute conflict for operator |_or_| (0 != 15).
warning strategy conflict for operator |_or-else_|.
warning attribute conflict for operator |_xor_| (0 != 15).
warning strategy conflict for operator |_implies_|.
warning attribute conflict for operator |sd/2| (0 != 2).

Do you know what is this? I tentatively apologize if this is some
current limitation which was explained to me before but maybe I forgot
about it.

Thanks,
Razvan
