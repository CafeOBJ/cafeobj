-- To: cafeteria@rascal.jaist.ac.jp
-- Subject: Re: cafeobj 1.4.1p7 
-- In-reply-to: Your message of "Wed, 20 May 1998 18:42:43 +0200."
--              <9805200942.AA01575@is27e0s07.jaist.ac.jp> 
-- Date: Thu, 21 May 1998 09:46:30 +0900
-- From: Makoto Ishisone <ishisone@srapc459.sra.co.jp>
-- Resent-Message-ID: <"R59nUC.A.c_G.4n3Y1"@rascal.jaist.ac.jp>
-- Resent-From: cafeteria@rascal.jaist.ac.jp
-- Reply-To: cafeteria@rascal.jaist.ac.jp
-- X-Mailing-List: <cafeteria@ldl.jaist.ac.jp> archive/latest/205
-- X-Loop: cafeteria@ldl.jaist.ac.jp
-- Precedence: list
-- Resent-Sender: cafeteria-request@rascal.jaist.ac.jp
-- Content-Type: text
-- Content-Length: 1339

-- >  |true : Bool
-- >  |(rtime 2236 utime 2196 stime 3 rewrite 44538 match 129489 gc 9 backtrack 250457
-- >  | backtrack-fail 0)
-- > 
-- > BTW, this looks to me that brute is still faster than Elan, or in the
-- > worst case very near Elan performance. Am I right?
-- Well, I don't think so.  For reductions involving AC matching, the
-- number of rewrites tends to be much larger in brute than in Elan,
-- maude or CafeOBJ interpreter, because of the difference of their
-- matching strategies.  In fact, the number of rewrites is only 6901
-- with maude (and it takes only 250ms).

-- Consider the following specification:

mod! AC {
  [ S ]
  ops a b c d : -> S
  op _+_ : S S -> S { assoc comm }
  var X : S
  eq X + X = X .
}

-- Now let's reduce term "a + b + c + d + a + b + c + d" with both interpreter
-- and brute.

-- Interpreter:
-- 	d + c + b + a : S
-- 	(0.010 sec for parse, 1 rewrites(0.000 sec), 3 matches)

-- Brute:
-- 	d + c + b + a : S
-- 	(rtime 103 utime 2 stime 0 rewrite 4 match 5 gc 0 backtrack 1 backtrack-fail 0)

-- The interpreter needs only 1 rewrite while brute needs 4.  This is
-- because brute only tries to match variable X against each single
-- subterm (in this case, a, b, c and d) to avoid excessive search.

-- So, brute is still much slower than maude in this regard, but I have
-- a simple idea to improve the performance.  Stay tuned..

-- 						-- ishisone@sra.co.jp

