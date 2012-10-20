-- : > I have some troubles with a simple example which seemed to be working
-- : > well in previous versions. It is the "classical" stacks:
-- :
-- : It seems that current version does work without errors.
-- : Here is a session log of 1.4(Beta-3):

-- Thank you for your answer. It is true I got the binaries, but today I
-- installed the version compiled here at JAIST by Iida-san, and I got
-- the same error!

-- I am sending you the complete files that I am using, maybe there is a
-- very subtle thing related to the user-defined naturals...?

-- Thanks,
-- Razvan

-- set auto context on
-- --------------------------------------------------------
-- file simple-nat.mod
-- --------------------------------------------------------

mod! BARE-NAT {

  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

mod! SIMPLE-NAT {
  protecting(BARE-NAT)

  op _+_ : Nat Nat -> Nat 
  
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . eq 0 + N:Nat = N .
}

red in SIMPLE-NAT : (s s 0) + (s s 0) .

mod! TIMES-NAT {
  protecting(SIMPLE-NAT)

  op _*_ : Nat Nat -> Nat

  vars M N : Nat 
    
  eq 0 * N = 0 .
  eq N * 0 = 0 .
  eq N * s(M) = (N * M) + N .
}

red in TIMES-NAT : (s s s 0) * (s s s s s 0) .

mod! NAT-OMEGA {
  extending(BARE-NAT)

  op omega :  -> Nat
  pred _<_ : Nat Nat 

  vars N M : Nat    
  
  eq s omega = omega .   eq N < omega = true .
  eq 0 < s N = true .
  cq s(M) < s(N) = true     if M < N .
}

select NAT-OMEGA .
red s s 0 < s s s s 0 .
red s s 0 < omega .
red omega < s s 0 .

mod! NAT-OMEGA+ {
  protecting(SIMPLE-NAT + NAT-OMEGA)

  eq omega + N:Nat = omega .   eq N:Nat + omega = omega .
}

red in NAT-OMEGA+ : (s s 0) + (s 0) < omega + s 0 .

mod! BARE-NNAT {
  extending(BARE-NAT)

  op _|_ : Nat Nat -> Nat {assoc}

  vars M N : Nat 

  eq s(M | N) = s(M) | s(N) .
    
  trans M | N => N .
  trans M | N => M .
}

red in BARE-NNAT : s( 0 | (s 0)) ==> s s 0 .

mod! SIMPLE-NNAT {
  protecting(BARE-NNAT + SIMPLE-NAT)

  vars M N N' : Nat 
  
  eq M + (N | N') = (M + N) | (M + N') .
  eq (N | N') + M = (N + M) | (N' + M) .
}

red in SIMPLE-NNAT : ((0 | (s 0)) + s( (s 0) | (s s s 0))) ==> (s s s 0) | (s s s s 0) .

mod! NNAT-OMEGA { protecting(NAT-OMEGA + BARE-NNAT) }


-- -----------------------------------------------------------
-- file hss.mod
-- -----------------------------------------------------------
-- example of behavioural specification featuring
-- a second order function, strict equality on hidden sorts
-- and an infinitary coinduction relation

-- in simple-nat

-- call  "history sensitive storage"

mod* HSS(X :: TRIV) {

  *[ Hss ]*

  bop put : Elt Hss -> Hss
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Elt

  var S : Hss
  var E : Elt

  eq get put(E, S) = E .
  beq rest put(E, S) = S .
}

mod HSS-NAT-PROOF {
  protecting(HSS + BARE-NAT)

  bop rest* : Hss Nat -> Hss 

  vars S S1 S2 : Hss
  vars N N' : Nat
  var E : Elt

  eq  [ p1 ] : rest*(S, s(N)) = rest*(rest S, N) .
  eq  [ p2 ] : rest*(S, 0) = S .
}

open HSS-NAT-PROOF .

-- op _R_ : Hss Hss -> Bool .
-- S1 R S2 iff for all N \in Nat we have get rest*(S1, N) == get rest*(S2, N)

-- we prove that _R_ is a hidden congruence 

  ops m n : -> Nat .
  ops e e1 e2 : -> Elt .
  ops s s1 s2 : -> Hss .

  eq [ hyp ] : get rest*(s1, N) = get rest*(s2, N) .

-- -----
--> get |
-- -----
start get s1 == get s2 .
eof

apply -.p2 within term .
apply .hyp within term .
apply reduce at term . -- it should be true

-- ------
--> put |
-- ------
-- we prove by case analysis on N 
-- eq get rest*(put(e, s1), N) = get rest*(put(e, s2), N) .

-- N = 0
red get rest*(put(e, s1), 0) == get rest*(put(e, s2), 0) .

-- N = s(n)
red get rest*(put(e, s1), s(n)) == get rest*(put(e, s2), s(n)) .

-- -----
--> rest |
-- -----
-- we prove that for all N 
-- eq get rest*(rest s1, N) = get rest*(rest s2, N) .

start get rest*(rest s1, n) == get rest*(rest s2, n) .
apply -.p1 within term .
apply .hyp within term .
apply reduce at term .

--> PROOF THAT _R_ IS A HIDDEN CONGRUENCE HAS BEEN SUCCESFULLY COMPLETED

-- ---------------------------------------------
--> proof of                                    |
--> beq rest rest put(E1, (put(E2, S))) = S .   |
-- ---------------------------------------------

red get rest*(rest rest put(e1, (put(e2, s))), n) == get rest*(s, n) .

-- ---------------------------------------------
--> proof of                                    |
--> beq   rest*(put(E, S), s(N)) = rest*(S, N) .|
-- ---------------------------------------------

red get rest*(rest*(put(e, s), s(m)), n) == get rest*(rest*(s, m), n) . 

close

-- some tests for the use of behavioural context condition in *reduce*
open HSS(NAT) .
  ops e e1 e2 :  -> Nat .
  ops st st1 st2 :  -> Hss . 
red rest(put(e, st)) == st .
red put(get(rest(put(e1, put(e2, st1)))), st2) == put(e2, st2) .
bred rest(put(e, st)) .
bred rest(put(e, st)) =b= st .
bred rest(put(e, st)) == st .
red rest(put(e, st)) =b= st .
red put(1 + 2, st) == put(3, st) .
close
