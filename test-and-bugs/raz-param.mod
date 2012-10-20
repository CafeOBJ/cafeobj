-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Fri, 3 Oct 97 09:58:36 GMT
-- Message-Id: <9710030958.AA11100@is27e0s07.jaist.ac.jp>
-- To: diacon@stoilow.imar.ro, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp, sawada@sra.co.jp
-- Subject:  suggestion for parameter instantiation implementation 
-- Content-Type: text
-- Content-Length: 1646

-- Dear Sawada-san and Nakagawa-san and Ishisone-san,

-- I have a couple of suggestions for parameter instantiation
-- implementation. Lets look at the following example:

mod* MON {
  protecting(TRIV)

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

view star from MON to INT {
  sort Elt -> Int,
  op null -> 0,
  op X:Elt ; Y:Elt -> X:Int + Y:Int - X * Y
}

mod* MONOID (X :: MON) { }

-- 1. I dont like that I have to write the trivial MONOID definition in
-- order to use the view *star*. Maybe we should have an abbreviation for
-- such situations, such as 

-- MON(star) 

-- 2. This is much more serious. I want to do a proof that *star* is
-- indeed a specification morphism. I want to run the following proof
-- score:

open MONOID(star) .
  ops x y z :  -> Int .
red (x ; y) ; z == x ; (y ; z) .
red x ; 0 == 0 .
red 0 ; x == 0 .
close

-- but I cannot since I dont have access to _;_ anymore... In the case of
-- derived operations this is a very severe problem, since I dont see how
-- I can use their definitions and the consequent power. In this case _;_
-- is like a notation for the derived operation on INT, so it should be
-- accessible somehow.

-- How about still keeping "in the shadow" the operations of the
-- parameters after instantiation? This means they are not really part of
-- the instantiated signature (you cannot see them even with the shallow
-- "show" commands), but they are still available as abbreviations. The
-- system should then supply some euqations encoding the view, in this
-- case 

-- eq X ; Y = X + Y - X * Y .
-- eq null = 0 . 

-- What do you think about this?

-- All the best!
-- Razvan
