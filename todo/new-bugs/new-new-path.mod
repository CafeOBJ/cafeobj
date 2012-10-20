-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Thu, 4 Jun 98 08:33:35 JST
-- Message-Id: <9806032333.AA06361@is27e0s07.jaist.ac.jp>
-- To: kokichi@jaist.ac.jp
-- Subject:  Re: new path.mod
-- Cc: s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Content-Type: text
-- Content-Length: 1904

-- Kokichi and Toshimi,

-- I further slightly modified the path example. I also have a suggestion
-- for the implementation, which I think it is minor but quite nice and
-- definitely a further step towards MEL.

-- What about after the reduction is finished and the normak form is
-- obtained, when printing the sort of the reusut, if the sort is ?S then
-- the system computes the predicate _: S and if results in true changes
-- the sort to S.

-- For example, in the path case it will be:

-- -- reduce in PATH(X <= GRAPH1) : e1 ; e2
-- e1 ; e2 : Path

-- rather than the current
-- -- reduce in PATH(X <= GRAPH1) : e1 ; e2
-- e1 ; e2 : ?Path

-- Here is the new path example.

-- Razvan
-- -----------------------------------------------------
-- FILE: /home/diacon/LANG/Cafe/prog/path.mod
-- CONTENTS: specification of a path data type featuring
--           partial functions
-- AUTHOR: Razvan Diaconescu (with inspiration from a Maude example)
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

  eq (E ; ?P) :is Path = (?P :is Path) and (s ?P) == (t E) .
  ceq s(E ; ?P) = s(E)  if (E ; ?P) :is Path .
  ceq t(E ; ?P) = t(?P) if (E ; ?P) :is Path .
}

-- a example of GRAPH
mod! GRAPH1 {
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
red e1 ; e2 . -- should be e1 ; e2 : Path
-- red (e1 ; e2) ; e3 == e1 ; (e2 ; e3) . -- should be true

eof
