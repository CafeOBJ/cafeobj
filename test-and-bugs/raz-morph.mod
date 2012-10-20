-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Fri, 3 Oct 97 09:36:23 GMT
-- Message-Id: <9710030936.AA11073@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  instantiation bug?
-- Content-Type: text
-- Content-Length: 529

-- Toshimi,

-- This is another thing that might be a bug (or some confusion from
-- me...).

-- Consider this specification of monoids:

mod* MON {
  protecting(TRIV)

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

view dual from MON to MON {
  op X:Elt ; Y:Elt -> Y:Elt ; X:Elt 
}

module! MONOID(X :: MON)
{
}

open MONOID(dual) * { op _;_ -> _|_ } .
   ops x y z :  -> Elt .
parse x | y . 

-- This gives an error, it seems it doesnt recognise the renaming. Have I
-- done something wrong here?

-- Thanks,
-- Razvan
