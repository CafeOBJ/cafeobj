-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sun, 5 Oct 97 04:57:22 GMT
-- Message-Id: <9710050457.AA11456@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  help with instantiation
-- Content-Type: text
-- Content-Length: 1380

-- Toshimi,

-- I bother you again with something about instantiations. There is
-- something I cannot understand, but maybe I am doing some very silly
-- mistake which I cannot see. Please tell me what I am doing wrong
-- here.

mod* MON (X :: TRIV)
{
  -- protecting(TRIV)

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

mod! LIST (extending X :: TRIV)
{
  -- extending(TRIV)

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq l:Elt ; null = l .   eq null ; l:Elt = l .
}

mod* MON-POW (POWER :: LIST, M :: MON)
{
  -- op _^_ : Elt.MON Elt.POWER -> Elt.MON
  op _^_ : Elt.M Elt.POWER -> Elt.M

  -- vars m m' : Elt.MON
  vars m m' : Elt.M
  vars p p' :  Elt.POWER

  eq (m ; m')^ p   = (m ^ p) ; (m' ^ p) .
  eq  m ^ (p ; p') = (m ^ p) ; (m ^ p') .
  eq  m ^ null     =  null .
}

view nat-as-list from LIST to NAT {
  sort Elt -> Nat,
  op _;_ -> _+_,
  op null -> 0 
}

open MON-POW(POWER <= nat-as-list) .
--  ops m m' :  -> Elt.MON .
 ops m m' :  -> Elt.M .
 ops n n' :  -> Nat . 
parse m ^ n .

-- and the system gives me an error!!

-- %MON-POW(POWER <= nat-as-list)(M.MON-POW)> parse m ^ n .
-- [Error]: no successfull parse
         
--          parsed:[_],rest:[_]:SyntaxErr  
--                 /             \          
--               m:Elt  ("^" "n"):Universal
                                         
         
-- (parsed:[ m ], rest:[ (^ n) ]) : SyntaxErr

-- I cannot understand what is going on. Please give me some hint.

-- With many thanks,
-- Razvan
