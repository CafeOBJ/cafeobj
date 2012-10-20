mod NAT' {
  [ Nat ]

  op 0 : -> Nat      
  op s : Nat -> Nat  
}

mod* STACK(X :: TRIV) {

  *[ Stack ]*

  bop push : Elt Stack -> Stack
  bop pop : Stack -> Stack
  bop top : Stack -> Elt

  var S : Stack
  var E : Elt

  eq top(push(E, S)) = E .
  beq pop(push(E, S)) = S .
}

mod PROOF1 {
  protecting(STACK + NAT')

  bop pop* : Stack Nat -> Stack 

  vars S S1 S2 : Stack
  vars N N' : Nat
  var E : Elt


  eq  [ p1 ] : pop*(pop(S), N) = pop*(S, s(N)) .
  eq  [ p2 ] : pop*(S, 0) = S .
}

open PROOF1 .

-- op _R_ : Stack Stack -> Bool .
-- S1 R S2 iff for all N \in Nat we have top(pop*(S1, N)) == top(pop*(S2, N))

-- we prove that _R_ is a hidden congruence by induction on N \in Nat

ops m n : -> Nat .
ops e e1 e2 : -> Elt .
ops s s1 s2 : -> Stack .

eq [ hyp ] : top(pop*(s1, N)) = top(pop*(s2, N)) .

-- -----
-- top |
-- -----
start top(s1) == top(s2) .
apply -.p2 within term .
apply .hyp within term .
apply reduce at term . -- it should be true

-- ------
-- push |
-- ------
-- we prove by induction on N 
-- eq top(pop*(push(e, s1), N)) = top(pop*(push(e, s2), N)) .

-- N = 0
red top(pop*(push(e, s1), 0)) == top(pop*(push(e, s2), 0)) .

-- N = s(n)

start top(pop*(push(e, s1), s(n))) == top(pop*(push(e, s2), s(n))) .
apply -.p1 within term .
apply reduce at term . -- it should be true

-- ----
-- pop |
-- ----
-- we prove that for all N 
-- eq top(pop*(pop(s1), N)) = top(pop*(pop(s2), N)) .

red top(pop*(pop(s1), n)) == top(pop*(pop(s2), n)) .

--> PROOF THAT _R_ IS A HIDDEN CONGRUENCE HAS BEEN SUCCESFULLY COMPLETED

-- --------------------------------------------
-- proof of                                    |
-- beq pop(pop(push(E1, (push(E2, S))))) = S . |
-- --------------------------------------------

red top(pop*(pop(pop(push(e1, (push(e2, s))))), n)) == top(pop*(s, n)) .

-- -------------------------------------------
-- proof of                                   |
-- beq   pop*(push(E, S), s(N)) = pop*(S, N) .|
-- -------------------------------------------

start top(pop*(pop*(push(e, s), s(m)), n)) == top(pop*(pop*(s, m), n)) .
apply -.p1 within term .
apply reduce at term .

close
