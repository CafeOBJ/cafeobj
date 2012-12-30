** -*- Mode:CafeOBJ -*-
--> sorting.mod , translated from OBJ3 example sorting.obj

require tiny-list
require lexl

module! SORTING(X :: POSET) {
  protecting (LIST(X))
  op sorting_ : List -> List 
  op unsorted_ : List -> Bool
  vars L L' L'' : List 
  vars E E' : Elt 
  cq sorting L = L if unsorted L =/= true .
  cq sorting L E L' E' L'' = sorting L E' L' E L'' if E' < E .
  cq unsorted L E L' E' L'' = true if E' < E .
}

open SORTING(NATD) .
reduce sorting(18 5 6 3) .       **> should contain: 3 6 18
reduce sorting(8 5 4 2) .        **> should contain: 2 4 8
reduce sorting(6 3 1) .          **> should be: 1 3 6
reduce sorting(18 6 5 3 1) .     **> should contain: 1 3 6 18
close

open SORTING(INT) .
reduce unsorted 1 2 3 4 .        **> should not be: true
reduce unsorted 4 1 2 3 .        **> should be: true
reduce sorting 1 4 2 3 .         **> should be: 1 2 3 4
close

make SORTING-PH-LIST (SORTING[(LEXL[QIDL]*{op __ -> _._})
 			      {sort Elt -> List,
			       op _<_ -> _<<_}])
-- make SORTING-PH-LIST (SORTING[(LEXL[QIDL]*{op __ -> _._})
-- 			      {sort Elt -> List}])

select SORTING-PH-LIST
reduce sorting (('b . 'a)('a . 'a)('a . 'b)) .
**> should be: ('a . 'a)('a . 'b)('b . 'a)

--
eof
-- 
$Id: sorting.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
