-- From: Alexander Knapp <knapp@informatik.uni-muenchen.de>
-- Date: Wed,  8 Oct 97 17:34:03 +0200
-- To: Toshimi Sawada <sawada@sra.co.jp>
-- Subject: Re: Transitions 
-- References: <199710061011.MAA06198@thales.pst.informatik.uni-muenchen.de> 
-- 	<199710081414.XAA10357@sras75.sra.co.jp>
-- Content-Type: text/plain
-- Content-Length: 1662

-- !

-- > I'm very sorry for this delaying reply. I'v been sticking into a very
-- > hard problem about parameterized modules, which is just a nightmare.
-- So I'm the more glad, you can reply at all.  Thanks.

-- > > ceq (context(inner(a)) ==> context(inner(a'))) = true
-- > > if (inner(a) ==> inner(a')) == true .
-- > System does add such axiom just for transitions which can be used as
-- > a rewrite rule, (perdon me if I'm wrong, I'm saying without check my
-- > implementation).
-- > This seems to be very interesting issue. Because I'm a lazy boy, would you
-- > please send me your specification, and let me know your exact intention.
-- I've heard about this and tried

module TEST {
  imports {
    protecting (RWL)
  }

  signature {
    [ Test ]

    ops a b c d : -> Test
    op _:=_ : Test Test -> Test
  }

  axioms {
    -- eq (a ==> b) = true .
    -- eq (b ==> c) = true .
    trans a => b .
    trans b => c .
    ctrans (X:Test := Z:Test) => (Y:Test := Z)
    if (X ==> Y) .
  }
}

-- and

-- CafeOBJ> select TEST

-- TEST> red a ==> c .
-- -- reduce in TEST : a ==> c
-- a ==> c : Bool
-- (0.000 sec for parse, 2 rewrites(0.020 sec), 12 match attempts)

-- TEST> red ((a ==> c) == true) .
-- -- reduce in TEST : (a ==> c) == true
-- false : Bool
-- (0.010 sec for parse, 3 rewrites(0.020 sec), 13 match attempts)

-- Problem is transitivity.  (My concrete intention is to encode structural  
-- rules in operational semantics, for example
--        e1 -> e2
--   ------------------
--   e1 := e -> e2 := e
-- I wanted to write
--   ctrans (e1 := e) => (e2 := e)
--            if (e1 ==> e2)
-- but that does not work because of the variable e2 in the condition that does  
-- not occur in the left-hand side of the rule; I'm looking for alternative  
-- formulations.)

-- Thanks,
-- Best regards,
-- Alexander.

-- --

-- Alexander Knapp
-- URL: http://www.pst.informatik.uni-muenchen.de/~knapp/
