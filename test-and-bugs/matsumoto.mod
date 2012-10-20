-- From: Michihiro Matumoto <mitihiro@jaist.ac.jp>
-- Date: Fri, 31 Oct 97 20:57:26 JST
-- Message-Id: <9710311157.AA01948@is27e0s04.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Cc: diacon@stoilow.imar.ro, ishisone@sra.co.jp.kokichi@jaist.ac.jp,
--         nakagawa@sra.co.jp, ogata@jaist.ac.jp.s_iida@jaist.ac.jp,
--         sawada@sra.co.jp
-- Cc: mitihiro@jaist.ac.jp
-- In-Reply-To: <199710301528.AAA13324@sras75.sra.co.jp> (message from Toshimi Sawada on Fri, 31 Oct 1997 00:28:15 +0900)
-- Subject: Re: Subject: Re: a couple of small beh specification corrections
-- Content-Type: text
-- Content-Length: 2345

-- Dear All,

-- > > Also I want the swith to select whether "default check" is executed.
-- > > Because, We can know whether "default check" succeed without
-- > > the execution of "default check". For example, by using Test Set
-- > > Coinduction.
-- > 
-- > I guess that "default check" means the proof of congruency of
-- > =*= done by the system in automatic manner. If so, providing the switch 
-- > which prohibits the proof can be done very easily.

-- Yes. "default check" means the proof of congruency of =*= done by
-- the system in automatic manner.

-- > If many of you agree with the above, I will implement it. 
-- > Does any other ones want such switch? Anyway, this switch will make no
-- > harm, I suspect.
-- > 

-- Please, execute CafeOBJ code which I sent in previous E-mail.
-- Perhaps, many of you will agree with my opinion.

-- > >   To sawada-san,
-- > >      In my memory -- I'm sorry that there is no CafeOBJ ver1.3 
-- > >    here now --, on CafeOBJ Ver1.3 following code succeeds, 
-- > >    but on CafeOBJ ver1.4b3 it fails. I think it may be bug.
-- > >    vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
-- > >      -- (4) len rq dq = 0, len lq dq = 0
-- > >      open .
-- > > 
-- > 
-- > Sorry, but I could not figure out why this is wrong. 
-- > Would you please let me know why?
-- > (There was a bug in `auto context change' mode in 1.4b3. But, for your
-- >  case, this bug does not affect. Please ask Razvan about this problem.
-- >  He also has a patch fixing it.)
-- > 

-- I'm sorry. This was a bad example.
-- This bug(?) is the bug of "bred command" not "red command".
-- I used "=b=" in "red command".

-- The same phenomenon occurs in following code.

-- open .
-- op e : -> Elt .
-- op dq : -> DoubleQueue .
-- eq len rq dq = 0 .
-- eq len lq dq = 0 .

-- bred rq pop put(e, dq) == rq dq .
-- close

-- The point that I think it is a bug is a folloing execution result.

-- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv

-- %DOUBLEQUEUE(X)> bred rq pop put(e, dq) .
-- -- behavioural reduce in %(X.DOUBLEQUEUE) : rq (pop put(e,dq))
-- pop put(e,rq dq) : ExtQueue
-- (0.017 sec for parse, 18 rewrites(0.000 sec), 62 match attempts)

-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-- Here, we assume that "eq len rq dq = 0 .".
-- So, I think "bceq pop put(E, Q) = Q if len Q == 0 ." in "QUEUE"
-- module must be matched to this result.

-- If so, "bred rq pop put(e, dq) == rq dq ." holds.

-- Yours sincerely,
-- Michihiro Matsumoto (mitihiro@jaist.ac.jp)
