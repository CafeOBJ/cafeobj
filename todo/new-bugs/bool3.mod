-- To: cafeteria@rascal.jaist.ac.jp
-- Subject: Re: cafeobj 1.4.1p7 
-- In-reply-to: Your message of "Wed, 20 May 1998 18:14:46 +0200."
--              <9805200914.AA01525@is27e0s07.jaist.ac.jp> 
-- Date: Wed, 20 May 1998 18:35:13 +0900
-- From: Makoto Ishisone <ishisone@srapc459.sra.co.jp>
-- Resent-Message-ID: <"bjz86C.A.VsE.XPqY1"@rascal.jaist.ac.jp>
-- Resent-From: cafeteria@rascal.jaist.ac.jp
-- Reply-To: cafeteria@rascal.jaist.ac.jp
-- X-Mailing-List: <cafeteria@ldl.jaist.ac.jp> archive/latest/202
-- X-Loop: cafeteria@ldl.jaist.ac.jp
-- Precedence: list
-- Resent-Sender: cafeteria-request@rascal.jaist.ac.jp
-- Content-Type: text
-- Content-Length: 1830

-- Dear Razvan-san,

-- > Is this the same as the bug which caused the filure of both the
-- > interpreter and the compiler at the recent cafeOBJ symposium (on the
-- > Elan benchmark example, the one with  De Morgan law)? If not, then was
-- > that detected and fixed? If yes, is it fixed in brute too?

-- As for brute, the bug revealed by Elan benchmark was fixed in version 0.99.
-- Shown below is the sample session.
-- 						-- ishisone@sra.co.jp
mod! BOOL3 {
  [ B3 ]
  ops (_+_) (_*_) : B3 B3 -> B3 { assoc comm }
  ops 0 1 2 : -> B3
  ops (_and_) (_or_) : B3 B3 -> B3 { r-assoc }
  op not : B3 -> B3
  ops a b c d : -> B3
    
  vars X Y Z : B3

  eq X + 0 = X .
  eq X + X + X = 0 .
  eq (X + Y) * Z = (X * Z) + (Y * Z) .

  eq X * 0 = 0 .
  eq X * X * X = X .
  eq X * 1 = X .

  eq X and Y = (X * X * Y * Y) + (2 * X * X * Y) +
    (2 * X * Y * Y) + (2 * X * Y) .
  eq X or Y = (2 * X * X * Y * Y) + (X * X * Y) +
    (X * Y * Y) + (X * Y) + (X + Y) .
  eq not(X) = (2 * X) + 1 .
  eq 2 = 1 + 1 .
}

-- ----------------------------------------------------------------------------
-- BOOL3> show BOOL3
-- module! BOOL3
-- {
--   imports {
--     protecting (BOOL)
--   }
--   signature {
--     [ B3 ]
--     op _ + _ : B3 B3 -> B3 { assoc comm r-assoc }
--     op _ * _ : B3 B3 -> B3 { assoc comm r-assoc }
--     op 0 : -> B3
--     op 1 : -> B3
--     op 2 : -> B3
--     op _ and _ : B3 B3 -> B3 { strat: (0 1 2) r-assoc }
--     op _ or _ : B3 B3 -> B3 { strat: (0 1 2) r-assoc }
--     op not : B3 -> B3 { strat: (0 1) }
--     op a : -> B3
--     op b : -> B3
--     op c : -> B3
--     op d : -> B3
--   }
--   axioms {
--     var X : B3
--     var Y : B3
--     var Z : B3
--     eq X + 0 = X .
--     eq X + X + X = 0 .
--     eq (X + Y) * Z = (X * Z) + (Y * Z) .
--     eq X * 0 = 0 .
--     eq X * X * X = X .
--     eq X * 1 = X .
--     eq X and Y = (X * X * Y * Y) + (2 * X * X * Y) + (2 * X * Y *
--          Y) + (2 * X * Y) .
--     eq X or Y = (2 * X * X * Y * Y) + (X * X * Y) + (X * Y * Y) +
--          (X * Y) + X + Y .
--     eq not(X) = (2 * X) + 1 .
--     eq 2 = 1 + 1 .
--   }
-- }

-- BOOL3> set tram path brute
--
-- BOOL3> tram red (not(a) and not(b) and not(c) and not(d)) == not(a or b or c or d) .
-- reduce in BOOL3 : not(a) and (not(b) and (not(c) and not(d))) 
--    == not(a or (b or (c or d)))

-- true : Bool
-- (rtime 2236 utime 2196 stime 3 rewrite 44538 match 129489 gc 9 backtrack 250457
--  backtrack-fail 0)
--
-- BOOL3> 
-- ----------------------------------------------------------------------------


