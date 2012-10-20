-- Date: Thu, 4 Jun 1998 00:05:29 +0900
-- From: Kokichi Futatsugi <kokichi@shin.jaist.ac.jp>
-- Message-Id: <199806031505.AAA00420@shin.jaist.ac.jp>
-- To: diacon@jaist.ac.jp
-- CC: s_iida@jaist.ac.jp, sawada@sra.co.jp
-- In-reply-to: <9806030821.AA06223@is27e0s07.jaist.ac.jp> (message from Razvan Diaconescu on Wed, 3 Jun 98 17:21:09 JST)
-- Subject: Re: new path.mod
-- Cc: kokichi@jaist.ac.jp
-- Reply-to: kokichi@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 1496

-- Razvan,

-- Here is my modification of your path example.  Modificationis is
-- marginal, and mainly for pedagogical purpose.

-- I just want to show a proper use of parameterization, for the system
-- supports parameterization with sufficient reliability.

-- Enjoy,  --KF

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- CONTENTS: specification of a path data type featuring
--           partial functions
-- AUTHOR: Razvan Diaconescu (with inspiration from a Maude example)
--		modified by --KF-980603
-- DIFFICULTY: **

-- a graph data type
mod* GRAPH {
  [ Node Edge ]

  ops (s_) (t_) : Edge -> Node 
}

-- the path data type 
mod! PATH (X :: GRAPH) {
  [ Edge < Path ]

  op _;_ : ?Path ?Path -> ?Path  {assoc}
  ops (s_) (t_) : Path -> Node 

  var  E : Edge 
  var  P : Path
  var ?P : ?Path 

  ceq (E ; ?P) :is Path = true  if (?P :is Path) and (s ?P) == (t E) .
  ceq s(E ; ?P) = s(E)  if (E ; ?P) :is Path .
  ceq t(E ; ?P) = t(?P) if (E ; ?P) :is Path .
}

-- a example of GRAPH
mod GRAPH1 {
  [ Node Edge ]

  ops (s_) (t_) : Edge -> Node 

  ops n1 n2 n3 :  -> Node 
  ops e1 e2 e3 :  -> Edge 
  eq s e1 = n1 .
  eq t e1 = n2 .
  eq s e2 = n2 .
  eq t e2 = n3 .
  eq s e3 = n3 .
  eq t e3 = n1 .
}

-- testing by some example reductions
select (PATH(GRAPH1))
red s (e1 ; e3) . -- should be error
red s (e1 ; e2) . -- should be n1
red t (e2 ; e3) . -- should be n1
red s (e1 ; e2 ; e3) . -- should be n1
red (e1 ; e2) ; e3 == e1 ; (e2 ; e3) . -- should be true

eof






