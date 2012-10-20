-- 3. Below you find the files with the module definitions and proof scores of
-- nthe mutual-exclusion example. Please let me know if you are interested in
-- another examples I tested. Now I try to update the paper "Understanding ..."
-- and I hope that in few days I will be able to send you a copy. 

-- Best regards,
-- Dorel.

-- ******************************************
mod! MUTEX-DATA {

  [ A-State B-State CR-State Config ]

**> operators

  ops A-bcs A-ecs A-bncs A-encs : -> A-State
  ops B-bcs B-ecs B-bncs B-encs : -> B-State
  ops av non-av : -> CR-State 
  op ___ : A-State B-State CR-State -> Config

**> variables

  var A : A-State 
  var B : B-State 
  var C : CR-State 

**> transitions

  trans [A-ncs] : A-bncs B C => A-encs B C .
  trans [A-pre] : A-encs B av => A-bcs B non-av .
  trans [A-cs] : A-bcs B C => A-ecs B C .
  trans [A-post] : A-ecs B C => A-bncs B av .

  trans [B-ncs] : A B-bncs C => A B-encs C .
  trans [B-pre] : A B-encs av => A B-bcs non-av .
  trans [B-cs] : A B-bcs C => A B-ecs C .
  trans [B-post] : A B-ecs C => A B-bncs av .
}


mod* MUTEX-OBJECT 
{
  protecting (MUTEX-DATA) 

  *[ State ]*

  bop A-in _ : State -> A-State 
  bop B-in _ : State -> B-State 
  bop CR-in _ : State -> CR-State 

  bops A-ncs A-pre A-cs A-post : State -> State
  bops B-ncs B-pre B-cs B-post : State -> State

  var Q : State

  eq A-in A-ncs(Q) = A-encs .
  eq A-in A-pre(Q) = A-bcs .
  eq A-in A-cs(Q) = A-ecs .
  eq A-in A-post(Q) = A-bncs .
  eq A-in B-ncs(Q) = A-in Q .
  eq A-in B-pre(Q) = A-in Q .
  eq A-in B-cs(Q) = A-in Q .
  eq A-in B-post(Q) = A-in Q .

  eq B-in B-ncs(Q) = B-encs .
  eq B-in B-pre(Q) = B-bcs .
  eq B-in B-cs(Q) = B-ecs .
  eq B-in B-post(Q) = B-bncs .
  eq B-in A-ncs(Q) = B-in Q .
  eq B-in A-pre(Q) = B-in Q .
  eq B-in A-cs(Q) = B-in Q .
  eq B-in A-post(Q) = B-in Q .

  eq CR-in B-ncs(Q) = CR-in Q .
  eq CR-in B-pre(Q) = non-av .
  eq CR-in B-cs(Q) = non-av .
  eq CR-in B-post(Q) = av .
  eq CR-in A-ncs(Q) = CR-in Q .
  eq CR-in A-pre(Q) = non-av .
  eq CR-in A-cs(Q) = non-av .
  eq CR-in A-post(Q) = av .
}
-- *****************************************
-- Theorem 1: MUTEX-OBJECT does not deadlock


-- -- Lemma 1: A can enter its critical section
open MUTEX-OBJECT
-- hypothesis
op q : -> State .
eq A-in q = A-encs . -- A ended its noncritical section
eq B-in q = B-encs . -- B ended its noncritical section
eq CR-in q = av .    -- CR is available

-- conclusion
red A-in q B-in q CR-in q ==> 
    A-in A-pre(q) B-in A-pre(q) CR-in A-pre(q) . -- it should be true
close

-- -- Lemma 2: B can enter its critical section
open MUTEX-OBJECT
-- hypothesis
op q : -> State .
eq A-in q = A-encs . -- A ended its noncritical section
eq B-in q = B-encs . -- B ended its noncritical section
eq CR-in q = av .    -- CR is available

-- conclusion
red A-in q B-in q CR-in q ==> 
    A-in B-pre(q) B-in B-pre(q) CR-in B-pre(q) . -- it should be true
close

-- -- Lemma 3: A and B cannot enter their critical sections in the same time
open MUTEX-OBJECT
-- hypothesis
op q : -> State .
eq [hyp1] : A-in q = A-encs . -- A ended its noncritical section
eq [hyp2] : B-in q = B-encs . -- B ended its noncritical section
eq [hyp3] : CR-in q = av .    -- CR is available

-- conclusion
start A-in q B-in q CR-in q . 
apply hyp1 within term .
apply hyp2 within term .
apply hyp3 within term .
-- rule MUTEX-DATA.11 is [a-pre] : A-encs B av => A-bcs B non-av 
apply MUTEX-DATA.11 within term . -- it could be applied
-- rule MUTEX-DATA.15 is [b-pre] : A B-encs av => A B-bcs non-av
apply MUTEX-DATA.15 within term . -- it couldn't be applied
close

open MUTEX-OBJECT
-- hypothesis
op q : -> State .
eq [hyp1] : A-in q = A-encs . -- A ended its noncritical section
eq [hyp2] : B-in q = B-encs . -- B ended its noncritical section
eq [hyp3] : CR-in q = av .    -- CR is available

-- conclusion
start A-in q B-in q CR-in q .  
apply hyp1 within term .
apply hyp2 within term .
apply hyp3 within term .
apply MUTEX-DATA.15 within term . -- it could be applied
apply MUTEX-DATA.11 within term . -- it couldn't be applied
close

