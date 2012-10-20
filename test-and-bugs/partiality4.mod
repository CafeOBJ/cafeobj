-- Date: Sun, 9 Nov 1997 17:21:03 +0200
-- From: Diaconescu Razvan <diacon@stoilow.imar.ro>
-- Message-Id: <9711091521.AA05426@stoilow.imar.ro>
-- To: sawada@sra.co.jp
-- Subject:  PS: partiality 
-- Cc: diacon@stoilow.imar.ro, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 834

-- I forgot to end you the last version of the pat specification. here it
-- is.

-- Razvan
-- ----------------------------------------------
mod* GRAPH {
  [ Node Edge ]

  ops (s_) (t_) : Edge -> Node 
}

mod! PATH (X :: GRAPH) {
  [ Edge < Path ]

  op _;_ : Path Path -> Path  { assoc }
  ops (s_) (t_) : Path -> Node 

  vars P P' : ?Path 
    
  ceq s(P ; P') = s P  if (s P') == (t P) .
  ceq t(P ; P') = t P' if (s P') == (t P) .
}

open PATH
  ops n1 n2 n3 :  -> Node .
  ops e1 e2 e3 :  -> Edge .
  eq s e1 = n1 .
  eq t e1 = n2 .
  eq s e2 = n2 .
  eq t e2 = n3 .
  eq s e3 = n3 .
  eq t e3 = n1 .
red s (e1 ; e3) . -- should be error
red s (e1 ; e2) . -- should be n1
red t (e2 ; e3) . -- should be n1
red s (e1 ; e2 ; e3) . -- it doesnt work for the moment 
red (e1 ; e2) ; e3 == e1 ; (e2 ; e3) . -- should be true
-- close 





