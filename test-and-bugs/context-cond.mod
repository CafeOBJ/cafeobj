-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sat, 29 Nov 97 20:19:18 JST
-- Message-Id: <9711291119.AA07588@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  beh context condition and coherence of operations
-- Content-Type: text
-- Content-Length: 1058

-- Dear Toshimi,

-- I tried again to run the example of hss with put as coherent operation
-- rather than bop. This time I used constants in terms rather than
-- variables (kill my laziness...). But there is another problem:

mod* HSS1(X :: TRIV) {

  *[ Hss ]*

  op put : Elt Hss -> Hss  
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Elt

  var S : Hss
  var E : Elt

  eq get put(E, S) = E .
  beq [beq]: rest put(E, S) = S .
}

-- testing the coherence of put in execution
open HSS1 .
  op e :  -> Elt .
  op s :  -> Hss . 
start get put(E, rest put(e, s)) .
apply .beq within term .
-- close

-- The system gives:

-- -- defining module* HSS1
-- [Warning]: redefining module HSS1 _*_*......._..*
-- ** system failed to prove =*= is a congruence of HSS1 done.
-- -- opening module HSS1(X).. done._*
-- result get put(E,s) : Elt

-- I think this rule should not be applied since it violates the
-- behavioural context condition. Of course, if

--   op put : Elt Hss -> Hss  { coherent }

-- then this computation is OK since for such reductions coherent
-- operators should be treated just as bops.

-- Razvan
