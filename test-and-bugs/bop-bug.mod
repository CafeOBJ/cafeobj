-- X-Loop: cafeteria@ldl.jaist.ac.jp
-- Precedence: list
-- Resent-Sender: cafeteria-request@rascal.jaist.ac.jp
-- Content-Type: text/plain; charset=US-ASCII
-- Content-Length: 1526

-- Dear Sawada-san,

-- It seems that "beq" in CafeOBJ-1.3.b6 is not propery implemented.
-- Please look into the following example:

-- ------------------------------------------------------------------
mod* STACK(X :: TRIV) {

  *[ Stack ]*

  op empty : -> Stack
  bop push : Elt Stack -> Stack
  bop pop : Stack -> Stack
  bop top : Stack -> Elt
  bop empty? : Stack -> Bool

  var S : Stack
  var E : Elt

  eq top(push(E, S)) = E .
  beq pop(push(E, S)) = S .
  eq empty?(empty) = true .
}
eof
-- ------------------------------------------------------------------

The system reports a error for "beq" as follows:

-- ------------------------------------------------------------------
-- CafeOBJ> in example2
-- processing input : ./example2.mod
-- defining module* STACK_.*........._.
[Error]: behavioural axiom must be constructed from terms of behavioural operators.*
-- failed to evaluate the form:
axiom declaration(equation): 
 lhs = (pop ( push ( E , S ) ))
 rhs = (S)

** returning to top level
-- ------------------------------------------------------------------

According to CafeOBJ report(version 0.93), the only condition for
behavioural sentences is:
  Operations on hidden sorts (other than constants) wich are not declared
  behavioural are prohibited from behavioural sentences.

The behavioural equation in above example only contains behavioural
operations (for variable, there is no restrictions). And I also found
there is a problem with constants. Could you please fix this bug?

Best Regards,
----
Shusaku Iida

