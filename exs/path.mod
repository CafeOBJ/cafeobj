-- -----------------------------------------------------
-- FILE: /home/diacon/LANG/Cafe/prog/path.mod
-- CONTENTS: specification of a path data type featuring
--           partial functions
-- AUTHOR: Razvan Diaconescu (with inspiration from a Maude example)
-- modfied by sawada@sra.co.jp for adapting to SRA implementation, i.e.,
-- sort membership predicate is `_:is_' not `_:_'.
--
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
set mel sort on
select PATH(GRAPH1)
red s (e1 ; e3) . -- should be error
red s (e1 ; e2) . -- should be n1
red t (e2 ; e3) . -- should be n1
red s (e1 ; e2 ; e3) . -- should be n1
red e1 ; e2 . -- should be e1 ; e2 : Path
red (e1 ; e2) ; e3 == e1 ; (e2 ; e3) . -- should be true
--
eof
--
$Id: path.mod,v 1.2 2007-01-27 23:18:38 sawada Exp $
