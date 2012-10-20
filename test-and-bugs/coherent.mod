-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sat, 29 Nov 97 20:19:17 JST
-- Message-Id: <9711291119.AA07586@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  testing the coherent operations
-- Content-Type: text
-- Content-Length: 1204

-- Dear Toshimi,

-- I am playing a bit with the new implementation of coherence.

-- HSS with coherent put
mod* HSS1(X :: TRIV) {

  *[ Hss ]*

  op put : Elt Hss -> Hss  -- { coherent }
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Elt

  var S : Hss
  var E : Elt

  eq get put(E, S) = E .
  beq [beq]: rest put(E, S) = S .
}

-- testing the coherence of put in execution
select HSS1
-- start get put(`E:Elt , rest put(`E':Elt, S)) .
start get put(`E:Elt , rest put(`E:Elt, `S:Hss)) .
apply .beq within term .

-- This gives

-- -- defining module* HSS1
-- [Warning]: redefining module HSS1 _*_*......._..*
-- ** system failed to prove =*= is a congruence of HSS1 done.
-- [Warning]: rule not applied
-- result get put(E,rest put(E':Elt,S)) : Elt

-- I think this should reduce actually because put is coherent. If put is
-- NOT coherent this behaviour is the correct one.

-- Razvan

-- PS. BTW I am now trying to promote the specification style with as
-- less bops as possible, i.e., use coherent operations instead of bops
-- whenever possible. Tnis has the advantgae of simplifying the proofs of
-- beh equivalent properties. HSS is a goo example, based on noticing
-- that put doesnt play any role in the defintion of beh equivalence. so
-- put is a method but which can be specified as coherent operation
-- rather than bop.
