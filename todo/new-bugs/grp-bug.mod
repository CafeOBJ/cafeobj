-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Fri, 17 Jul 98 15:48:07 JST
-- Message-Id: <9807170648.AA13166@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  apply under renaming situations
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 1613

-- Dear Toshimi,

-- I am trying to bring the wonderful grouops example by ATN closer ot
-- the usual mathematical practive and intuitions. For example, since
-- homorphimsms should be thought always together with their source and
-- target, some parameterization is needed. But this requires some sort
-- renaming and I have the feeling that apply does not work well under
-- such circumstances. However, I might miss the solution to this due to
-- my lack of enough skill in using apply. I might also misunderstand the
-- situation completely; in this case please let me know.

-- Here is the code:

module* GROUP {
  [ G ]
  op 0 : -> G
  op _+_ : G G -> G { assoc }
  op -_ : G -> G
  var X : G
  eq [r-id]: X + 0 = X .
  eq [r-inv]: X + (- X) = 0 .
}

module* G-HOM (G :: GROUP,
	       G' :: GROUP *{ sort G -> G' })
{
  op _h : G -> G'
  vars U V : G
  eq [hom] : (U + V) h = (U h) + (V h) .
}

** eof

** Theorem 6 (preserve neutral): 0 h = 0
open G-HOM
start 0 h == 0 .
-- apply -GROUP.r-id at (1) .
-- apply -GROUP.r-inv with X = (0 h) at (1 2) .
apply -G'.r-id at (1) .
apply -G'.r-inv with X = (0 h) at (1 2) .
apply -.hom at [1 .. 2] of (1) .
apply reduce at term .
close
**
eof

I get the following:

-- opening module G-HOM(G, G').. done.
[Warning]: rule not applied
result 0 h == 0 : Bool
[Warning]: no such occurrenct, occurrence (1
                                           2) is not correct for term :
    0 h == 0
    ignoring it.
[Warning]: term sort is incompatible with variable sort
    variable X:G
    term 0 h:G'
Error: Attempt to take the car of 156388 which is not listp.
  [condition type: simple-error]

[changing package from "COMMON-LISP-USER" to "CHAOS"]
[1] CHAOS(1):

-----
Thanks,
Razvan

