-- Date: Wed, 20 May 1998 14:48:10 +0200
-- From: Alexander Knapp <knapp@informatik.uni-muenchen.de>
-- Organization: Ludwig-Maximilians-Universit舩 Mchen
-- X-Mailer: Mozilla 4.04j2 [en] (X11; I; Linux 2.0.33 i686)
-- MIME-Version: 1.0
-- To: Toshimi Sawada <sawada@sra.co.jp>
-- Subject: Re: cafeobj 1.4.1p7
-- References: <199805200802.RAA06896@sras75.sra.co.jp>
-- Content-Transfer-Encoding: 7bit
-- Content-Type: text/plain; charset=us-ascii
-- Content-Length: 2392

-- Dear Toshimi!

-- > A new interpter (version 1.4.1(p7)) is available from
-- >         ftp://ftp.sra.co.jp/pub/lang/CafeOBJ/cafeobj-1.4.1p7.tar.gz
-- I'm happy to see that further progress has been made in the CafeOBJ
-- project.  Unfortunately I encountered the following problem:

-- This specification of sets works fine:

-- module SET[X :: TRIV] {
--   signature {
--     [ Elt < Set ]

--     op empty : -> Set
--     op __ : Set Set -> Set { assoc comm idem id: empty }
--     op _in_ : Elt Set -> Bool
--     op _-_ : Set Set -> Set
--   }

--   axioms {
--     eq e:Elt in empty = false .
--     cq e:Elt in (e':Elt m:Set) = true
--        if (e == e') .
--     cq e:Elt in (e':Elt m:Set) = e in m
--        if (e =/= e') .

--     cq (e:Elt m:Set) - m':Set = m - m'
--        if (e in m') .
--     cq (e:Elt m:Set) - m':Set = e (m - m')
--        if (not (e in m')) .
--     eq empty - m':Set = empty .
--   }
-- }

-- But this one (where I do not declare idem for __ but write idempotency
-- as an axiom; and that worked with cafeobj 1.4b5)

module SET[X :: TRIV] {
  signature {
    [ Elt < Set ]

    op empty : -> Set
    op __ : Set Set -> Set { assoc comm id: empty }
    op _in_ : Elt Set -> Bool
    op _-_ : Set Set -> Set
  }

  axioms {
    eq (e:Elt m:Set) (e:Elt m':Set) = e m m' .

    eq e:Elt in empty = false .
    cq e:Elt in (e':Elt m:Set) = true
       if (e == e') .
    cq e:Elt in (e':Elt m:Set) = e in m
       if (e =/= e') .

    cq (e:Elt m:Set) - m':Set = m - m'
       if (e in m') .
    cq (e:Elt m:Set) - m':Set = e (m - m')
       if (not (e in m')) .
    eq empty - m':Set = empty .
  }
}

-- produces

--              -- CafeOBJ system Version 1.4.1(p7) --
--                built: 1998 May 20 Wed 10:31:24 GMT
--                       prelude file: std.bin
--                                ***
--                   1998 May 20 Wed 12:45:17 GMT
--                          Type ? for help
--                                ---
--                    uses GCL (GNU Common Lisp)
--             Licensed under GNU Public Library License
--               Contains Enhancements by W. Schelter
-- processing input : ./rm.mod
-- -- defining module SET_*_*..._..._.......*
-- Error: NIL is not of type (OR RATIONAL FLOAT).
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by >.
-- Broken at >.  Type :H for Help.
-- CHAOS>>

-- Thanks in advance for your help,
-- Best regards,
-- Alexander.

-- -- 

-- Alexander Knapp
-- URL: http://www.pst.informatik.uni-muenchen.de/~knapp/
