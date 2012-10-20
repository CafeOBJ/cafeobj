-- Date: Thu, 13 Nov 1997 08:14:28 +0200
-- From: Diaconescu Razvan <diacon@stoilow.imar.ro>
-- Message-Id: <9711130614.AA03229@stoilow.imar.ro>
-- To: sawada@sra.co.jp
-- Subject:  new CafeOBJ release
-- Cc: ishisone@sra.co.jp, kokichi@jaist.ac.jp, mitihiro@jaist.ac.jp,
--         nakagawa@sra.co.jp, ogata@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 3922

-- Toshimi,

-- Thanks a lot for the new revised monoid lib. Just tell you that I
-- agree with all your comments and changes. I will try it myself with
-- the new system release, then maybe we can go further and extend this
-- lib for checking more sophisticated situations. It already gave us
-- much feedback, I think.

-- Since you mentioned the new release, may I ask you for the
-- confirmation about one of the message proposing some little changes in
-- dealing with beh stuff (I am not sure even that you received it; I am
-- inserting it at the end of this message).

-- Best regards,
-- Razvan
-- -----------------------------------------------------------------------
-- Dear All,

-- I am going to propose a couple of small beh specification corrections
-- that will make CafeOBJ more coherent and will improve a bit its
-- execution.
-- --------------------------------------
-- 1. The message about whether the checking for =*= is succesful or it
-- fails should be FOR THE MODULE rather than for individual
-- sorts. Conceptually the congruence for one sort doesnt make sense, the
-- concept of congruence is linked to the whole signature involved. For
-- example, if for at least one sort the checking of =*= fails one cannot
-- use it for the other sorts either. 

-- So, when CafeOBJ loads a beh module <module-name> then the message
-- shoud be like: 

-- * system failed to prove =*= is a congruence of <module-name>.

-- or

-- * system already proved =*= is a congruence of <module-name>.
-- ---------------------------------------
-- 2. This has to do with the behavioural coherence operations which were
-- discussed in the last workshop (also Grant and Joseph mentioned there
-- importance for beh specification especially in the context of
-- non-determinism and concurrency).

-- A BEHAVIOURAL COHERENT OPERATION is an operation
-- - on hidden sorts
-- - but which is NOT bop
-- - and preserves the beh equivalence (although not taking part in the
--   dfn of beh equiv since is not bop) 

-- The last condition is crucial since it makes those operation from "bad
-- guys" into "good guys".

-- For example ordinary equation deduction is sound only if all
-- operations on hidden sorts which are not bops are beh coherent. Also,
-- the beh context condition CAN BE RELAXED to include beh coherent
-- operations as "good guys".

-- At the level of CafeOBJ design I think we should adopt the following:

-- * declare beh coherence as an attribute of a bop (not makes sense for op)
-- * check the preservation of beh equivalence by a proof score (system
--   should not do anything about this) in order to support such declaration
-- * if the user "lies" (i.e. declare coherence but he didnt prove it or
--   the proof is wrong then he has to support the consequences...
-- * the implementation of behavioural context condition should be
--   relaxed such that to include coherent operations as "good guys" in
--   the condition, i.e., just as bops.

-- This is a very simple example:

mod* NNAT {
  protecting(NAT)

  *[ NNat ]*

  op [_] : Nat -> NNat
  op _|_ : NNat NNat -> NNat   --   { coherent }
  bop _->_ : NNat Nat -> Bool

  vars S1 S2 : NNat
  vars M N : Nat

  eq [M] -> N = M == N .
  eq S1 | S2 -> N = S1 -> N or S2 -> N .
}

--> the behavioural equivalence is =*=
--  (already automatically proved by the system)  
--> s =*= s' == (forall n:Nat) s -> n iff s' -> n

--> we  prove that _|_ is beh coherent
open NNAT .
  ops s1 s1' s2 s2' :  -> NNat .
  op n :  -> Nat .

--> s1 =*= s1' and s2 =*= s2'
  var N : Nat
  eq s1 -> N = s1' -> N .
  eq s2 -> N = s2' -> N .
red (s1 | s2) -> n == (s1' | s2') -> n . 

close

-- Other VERY FAMOUS example of behavioural coherent operations are the
-- coinduction relations which can be expressed directly in CafeOBJ

-- _R_ : hsort hsort -> Bool

-- The fact that they are congruence with respect to all bops means
-- exactly this! So, you can imagine that they can be used more
-- effectvely in proofs if after proving them we declare them coherent.

-- This is all, I am looking forward for your response!

-- Best regards,
-- Razvan
