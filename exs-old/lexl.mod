** -*- Mode:CafeOBJ -*-
-- from OBJ3 example 
--
require tiny-list
require views

module! LEXL(X :: POSET)
     principal-sort List
{
  protecting (LIST[X])
  op _<<_ : List List -> Bool 
  vars L L' : List 
  vars E E' : Elt 
  eq L << nil = false .
  eq nil << E L = true .
  eq E L << E L' = L << L' .
  cq E L << E' L' = E < E' if E =/= E' .
}

make LEXL-NATG (LEXL[NATG])

make NAT-LEXL (LEXL[NAT])

make NATD-LEXL (LEXL[NATD])

make PHRASE-LIST (
  LEXL[(LEXL[QIDL]*{op __ -> _._})
       { sort Elt -> List,
         op _<_ -> _<<_ }
      ]
)
--
eof
**
$Id: lexl.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
