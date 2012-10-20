-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Fri, 27 Mar 98 15:07:12 JST
-- Message-Id: <9803270607.AA06781@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  simplified version of the bug example on parameterization
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 1132

-- Dear Toshimi,

-- I somehow simplified the bug example sent before by Kokichi by
-- isolating the problem. So, this is the thing:

mod! STRG (X :: TRIV) { [ Elt < Strg ] }

mod* POSET { [ Elt ] }

mod! I-POSET (Y :: POSET)
  principal-sort 2Tuple {
  protecting(2TUPLE(Y,NAT))
}

mod! STRG-I-POSET (Z :: POSET) { pr(STRG(I-POSET(Z))) }

-- STRG-I-POSET(Z)> describe .
-- ======================================================================
--                      module STRG-I-POSET(Z)
--                           kind: object
--                        type: user defined
--               created: 1998 Mar 27 Fri 5:53:09 GMT
-- ----------------------------------------------------------------------

--                         << parameters >>
--   argument Z : protecting POSET
  

--                         << submodules >>
--   protecting (STRG(X <= I-POSET(Y <= Z)))

--                 << sorts and subsort relations >>
--   * visible sorts :
--     Elt, Elt < Strg
--     2Tuple
--     Strg, Elt < Strg

-- .........................................................

-- The problem is that Elt should not be < Strg, but 2Tuple should be <
-- Strg.

-- Best regards,
-- Razvan
