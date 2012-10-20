-- .Sender: knapp@jive.pst.informatik.uni-muenchen.de
-- Message-ID: <35631A27.CE37E666@informatik.uni-muenchen.de>
-- Date: Wed, 20 May 1998 20:00:07 +0200
-- From: Alexander Knapp <knapp@informatik.uni-muenchen.de>
-- Organization: Ludwig-Maximilians-Universit舩 Mchen
-- X-Mailer: Mozilla 4.04j2 [en] (X11; I; Linux 2.0.33 i686)
-- MIME-Version: 1.0
-- To: Toshimi & <sawada@sras75.sra.co.jp>
-- Subject: Re: cafeobj 1.4.1p7
-- References: <199805200802.RAA06896@sras75.sra.co.jp> <3562D10A.DF85C109@informatik.uni-muenchen.de>  <199805201309.WAA07433@sras75.sra.co.jp> <199805201629.BAA07591@sras75.sra.co.jp>
-- Content-Transfer-Encoding: 7bit
-- Content-Type: text/plain; charset=us-ascii
-- Content-Length: 1139

-- Dear Toshimi!

-- > And, as you reported, the system on GCL failed!
-- > I will examine the problem soon. 
-- OK, wonderful, I applied your procedure, now everything is fine. 
-- Thanks!

-- But, getting more bold, some time ago I sent you a problem description
-- about parameters and instantion.  Here it is again, tested for the new
-- version (where part of it has been solved):

-- --
module TEST {
  signature {
    [ M ]

    op c : -> M
  }
}


module TESTPAR[P :: TEST] {
  signature {
    record Test {
      attr : M
    }
  }
}

module TESTINST {
  imports {
    protecting (TESTPAR(NAT) * { sort M -> Nat, op c -> p(s(0)) })
  }
}
--
eof

If I select TESTINST, the following happens:

--
CafeOBJ> select TESTINST

TESTINST> red makeTest(attr = 0) .
-- reduce in TESTINST : makeTest(attr = 0)
Error: Caught fatal error [memory may be damaged]
Fast links are on: do (si::use-fast-links nil) for debugging
Error signalled by CAFEOBJ-EVAL-REDUCE-PROC.
Broken at PERFORM-REDUCTION.  Type :H for Help.
CHAOS>>:q
--

I would appreciate any hint.

Thanks again,
Best regards,
Alexander.

-- 

Alexander Knapp
URL: http://www.pst.informatik.uni-muenchen.de/~knapp/
