-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Wed, 3 Jun 98 17:09:57 JST
-- Message-Id: <9806030809.AA06204@is27e0s07.jaist.ac.jp>
-- To: s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Subject:  new path.mod
-- Cc: kokichi@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 1456

-- I just updated the path.mod example for the library in order to
-- reflect the new power of the interpreter. This consisting in deleating
-- the last part (after eof) and correcting a small typo reported by
-- Toshimi.

-- I plan to write also a bigger example of partiality. You can guess
-- what, some category theory, since it plays such an important role in
-- our life... Stay tuned. 

-- Razvan
-- -----------------------------------------
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

  ceq (E ; ?P) :is Path = true  if (?P :is Path) and (s ?P) == (t E) .
  ceq s(E ; ?P) = s(E)  if (E ; ?P) :is Path .
  ceq t(E ; ?P) = t(?P) if (E ; ?P) :is Path .
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
red s (e1 ; e2 ; e3) . -- should be n1
red (e1 ; e2) ; e3 == e1 ; (e2 ; e3) . -- should be true
close

