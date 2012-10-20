-- 2. Below is an example adapted  from the latest Joseph's message:
-- *****************************************
mod* CH {
  protecting(NAT)
  *[St]*

    op _   : Nat    -> St
    -- op n : Nat -> St
    bop _|_ : St Nat -> St
    bop [_] : St     -> Nat
    var S : St
    var N : Nat
    eq [n(N)] = N .
    eq [S | N] = N .
    eq [S | N] = [S] .
}
eof

-- ******************************************
-- The response of the system is:
-- ******************************************
-- defining module* CH......._
[Error]: No parse for axiom (ignored): 
 No possible parse for LHS
- possible RHS
         
         N:Nat
               
         
-- failed to evaluate the form:
axiom declaration(EQUATION): 
 lhs = ([ N ])
 rhs = (N)

-- ** returning to top level
-- *******************************************
-- The first operation makes each term of sort 'Nat' ambigous: it can be also
-- interpreted as being of sort 'St'. The actual version of  CafeOBJ cannot
-- manipulate this ambiguity. I think that in the context '[_]' every 'Nat'
-- term must (can?) be interpreted as being of sort 'St'. Which is your opinion
-- about this issues?
--
