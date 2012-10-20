-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Wed, 5 Nov 97 21:27:54 JST
-- Message-Id: <9711051227.AA04442@is27e0s07.jaist.ac.jp>
-- To: diacon@stoilow.imar.ro, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Subject:  order sortedness example 
-- Content-Type: text
-- Content-Length: 959

-- I am trying to run some partiality problem. Consider the follwoing
-- path specification:
set auto context on

mod* GRAPH {
  [ Node Edge ]

  ops (s_) (t_) : Edge -> Node 
}

mod! PATH (X :: GRAPH) {
  [ Edge < Path < EPath ]

  op _;_ : Path Path -> Path  { assoc }
  op _;_ : EPath EPath -> EPath { assoc }
  ops (s_) (t_) : Path -> Node 
  vars P P' : Path 
    
  ceq s(P ; P') = s P  if (s P') == (t P) .
  ceq t(P ; P') = t P' if (s P') == (t P) .
}

open .
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

-- How can we make

-- red s (e1 ; e2 ; e3) .

-- to give n1 ?

-- It seems in OBJ3 the retract mechanism allows such things.  

-- Best regards,
-- Razvan
