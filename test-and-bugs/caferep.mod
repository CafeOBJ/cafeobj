** --------------------------------------------
-- Some Examples of `CafeOBJ Report (v. 0.98.3)
** --------------------------------------------

** Example 1

module! BARE-NAT
{
  [ NzNat Zero < Nat ]
  op 0 : -> Zero
  op s_ : Nat -> NzNat
}

module* HSS-BNAT {
  protecting (BARE-NAT)
  *[ Hss ]*
  bop put : Nat Hss -> Hss
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Nat
}

** Example 9

module LIST-BNAT {
  protecting (BARE-NAT)
  [ NList < List ]
  op nil : -> List
  op _._ : Nat List -> NList
  op car_ : NList -> Nat
  op cdr_ : NList -> List
  var L : List
  var N : Nat
  eq car (N . L) = N .
  eq cdr (N . L) = L .
}

** Example 10

module! ULIST-BNAT {
  protecting (LIST-BNAT)
  trans N:Nat.BARE-NAT . L:List => L .
}

** Example 11

module* HSS-BNAT
{
  protecting (BARE-NAT)
  *[ Hss ]*
  bop put : Nat Hss -> Hss
  bop rest_ : Hss -> Hss
  bop get_ : Hss -> Nat

  var S : Hss
  var E : Nat
  eq get put(E,S) = E .
  eq rest put(E,S) = S .
}

module HSS-BNAT-PROOF {
  protecting (HSS-BNAT)
  bop rest* : Hss Nat -> Hss

  var S : Hss
  var N : Nat
  eq [p1]: rest*(S, s(N)) = rest*(rest S, N) .
  eq [p2]: rest*(S, 0) = 0 .
}

** Example 13

module! ULIST#-BNAT 
{
  protecting (ULIST-BNAT)
  op #_ : List -> Nat
  eq # nil = 0 .
  eq # (N:Nat . L:List) = s(# L) .
}

** Example 16

module! NAT-OMEGA 
{
  extending (BARE-NAT)
  op omega : -> Nat
  pred _<_ : Nat Nat

  vars N M : Nat
  eq s(omega) = omega .
  eq N < omega = true .
  eq 0 < s(N) = true .
  ceq s(M) < s(N) = true if M < N .
}

module! BARE-NNAT {
  extending (BARE-NAT)
  op _|_ : Nat Nat -> Nat {assoc}
  vars M N : Nat

  eq s(M | N) = s(M) | s(N) .
  trans M | N => N .
  trans M | N => M .
}

** Example 18
-- module* TRIV
-- {
--   [ Elt ]
-- }
module* MON {
  -- why imports TRIV rather than prameterized.
  --  protecting(TRIV)
  op _;_ Elt Elt -> Elt {assoc}
  op null : -> Elt
  eq m:Elt ; null = m .
  eq null ; m:Elt = m .
}


module! STRG 
{
  extending (TRIV)
  op _;_ : Elt Elt -> Elt {assoc}
  op null : -> Elt
  eq s:Elt ; null = s .
  eq null ; s:Elt = s .
}

module! STRG1
{
  protecting (TRIV)
  [ Elt < Strg ]
  op _;_ : Strg Strg -> Strg {assoc}
  op null : -> Strg
  eq s:Strg ; null = s .
  eq null ; s:Strg = s .
}

** Example 19

module! SIMPLE-NAT
{
  protecting (BARE-NAT)
  op _+_ : Nat Nat -> Nat
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N .
  eq 0 + N:Nat = N .
}

module NAT-OMEGA+
{
  extending (SIMPLE-NAT)
  protecting (NAT-OMEGA)
  eq omaga + N:Nat = omega .
  eq N:Nat + omega = omega .
}

** Example 21 

view bare-nat from TRIV to BARE-NAT
{
  sort Elt -> Nat
}

view plus from MON to SIMPLE-NAT {
  sort Elt -> Nat,
  op _;_ -> _+_,
  op null -> 0
}

view star from MON to INT {
  sort Elt -> Int,
  op null -> 0,
  op X:Elt ; Y:Elt -> X:Int + Y:Int - X * Y
}

** Example 22

module* MON* (Y :: TRIV) {
  op _;_ : Elt Elt -> ELt {assoc}
  op null : -> Elt

  eq m:Elt ; null = m .
  eq null ; m:Elt = m .
}

module! STRG1* (X :: TRIV)
{
  [ Elt < Strg ]
  op _;_ : Strg Strg -> Strg {assoc}
  op null : -> Strg
  eq s:Strg ; null s .
  eq null ; s:Strg = s .
}

module! STRG* (extending X :: TRIV) 
{
  op _;_ : Elt Elt -> Elt {assoc}
  op null : -> Elt

  eq s:Elt ; null = s .
  eq null ; s:Elt = s .
}

** Example23

module* MON-POW (POWER :: MON, M :: MON)
{
  op _^_ : Elt.M Elt.POWER -> Elt.M
  vars m m' : Elt.M
  vars p p' : Elt.POWER

  eq (m ; m) ^ p = (m ^ p) ; (m' ^ p) .
  eq m ^ (p ; p') = (m ^ p) ; (m ^ p') .
  eq m ^ null = null
}

** Example 24

module* MON-LINEAR (S :: MON, V :: MON)
{
  op _^_ : Elt.S Elt.V -> Elt.V

  vars s s' : Elt.S
  vars v v' : Elt.V
  eq s ^ (v; v') = (s ^ v); (s ^ v') .
  eq s ^ (s' ^ v) = s(s ; s') ^ v .
  eq null ^ v = v .
  eq s ^ null = null .
}

module! MON-LINEAR! (S :: MON, extending V :: MON)
{
  op _^_ : Elt.S Elt.V -> Elt.V

  vars s s' : Elt.S
  vars v v' : Elt.V
  eq s ^ (v; v') = (s ^ v); (s ^ v') .
  eq s ^ (s' ^ v) = s(s ; s') ^ v .
  eq null ^ v = v .
  eq s ^ null = null .
}

** Example 25

module! MON*-LINEAR (S :: MON*, V :: MON*){
  op _^_ : Elt.S Elt.V -> Elt.V

  vars s s' : Elt.S
  vars v v' : Elt.V
  eq s ^ (v; v') = (s ^ v); (s ^ v') .
  eq s ^ (s' ^ v) = s(s ; s') ^ v .
  eq null ^ v = v .
  eq s ^ null = null .
}

** Example 26

view nat;to+ from MON*(bare-nat) to SIMPLE-NAT {
  op _;_ -> _+_ ,
  op null -> 0 
}

** Example 27

module! STRG1#* (X :: TRIV)
{
  protecting (STRG1*(X) + SIMPLE-NAT)
  
  op #_ : Strg -> Nat

  eq # null = 0 .
  eq # E:Elt = s 0 .
  eq # (S1:Strg ; S2:Strg) = (# S1) + (# S2) .
}

module! STRG1-BNAT 
{
  [ Nat < Strg ]
  op _;_ : Strg Strg -> Strg {assoc}
  eq null : -> Strg
  eq s:Strg ; null = s .
  eq null ; s:Strg = s.
}

** Example 28

module! STRG1#-BNAT 
{
  protecting (STRG1-BNAT + SIMPLE-NAT)
  op #_ : Strg -> Nat
  eq # null = 0 .
  eq # E:Nat = s 0 .
  eq # (S1:Strg ; S2:Strg) = (# S1) + (# S2) .
}

module! STRG-BNAT
{
  extending (BARE-NAT)
  op _;_ : Nat Nat -> Nat { assoc }
  op null : -> Nat
  eq s:Nat ; null = s .
  eq null ; s:Nat = s .
}

** Example 29

-- MON-LINER(S <= strg-of-bnat)

view strg-of-bnat from MON to STRG1*(bare-nat)
{ sort Elt -> Strg}

-- MON-LINEAR(V <= plus)

-- MON-LINEAR(S <= strg-of-bnat, V <= plus)

module! TIMES-NAT
{
  protecting (SIMPLE-NAT)
  op _*_ : Nat Nat -> Nat
  vars M N : Nat

  eq 0 * N = 0 .
  eq N * 0 = 0 .
  eq N * s(N) = (N * M) + N .
}

view ^as* from MON-LINEAR(strg-of-bnat, plus) to TIMES-NAT
{
  sort Nat.S -> Nat,
  sort Nat.V -> Nat,
  op N1:Nat.S ^ N2:Nat.V -> N1:Nat * N2:Nat
}

** Example 30

view dual* from MON* to MON* {
  op X:Elt ; Y:Elt -> Y:Elt ; X:Elt
}

** Example 31

module* DATA
{
  [ Data ]
  op _+_ : Data Data -> Data
}

module* COUNTER(X :: DATA)
{
  *[ Counter ]*
  bop add : Data Counter -> Counter
  bop read_ : Counter -> Data

  eq read add(N:Data, C:Counter) = read(C) + N .
}

module* COUNTER-NAT
{
  protecting (COUNTER(SIMPLE-NAT))
}

module! SIMPLE-NNAT {
  protecting (BARE-NNAT + SIMPLE-NAT)
  eq M +(N | N') = (M + N) | (M + N') .
  eq (N | N') + M = (N + M) | (N' + M) .
}

module* COUNTER-NNAT
{
  protecting (COUNTER(SIMPLE-NNAT))
}

** Example 32

module* SRNG
{
  protecting (MON-POW * { sort Elt.POWER -> Strng,
			  sort Elt.M -> Strng,
			  op (_;_).POWER -> _+_,
			  op (_;_).M -> _+_,
			  op null.POWER -> 0,
			  op null.M -> 0,
			  op _^_ -> _*_ }
	      )
}

--
-- currently, map of `param' is obsolete.
-- 
module* STRNG 
{
  protecting (MON-POW * { param POWER -> M+,
			  param M -> M+}
	      * { sort Elt -> Srng,
		  op _;_ -> _+_,
		  op null -> 0,
		  op _^_ -> _*_
		})
}

** Example 33

module* MON-POW-NAT
{
  protecting (MON-POW(POWER <= plus))

  eq m:Elt.M ^ s(0) = m .
}

module* NAT-TIMES
{
  protecting (MON-POW-NAT(M <= plus) *
		{ sort Nat.M -> Nat,
		  sort Nat.POWER -> Nat,
		  op 0.M -> 0,
		  op 0.POWER -> 0,
		  op _^_ -> _*_ }
	      )
}

view nat-times from MON to NAT-TIMES {
  sort Elt -> Nat,
  op 0 : -> s(0),
  op _;_ -> _*_
}

modle* NAT-POW {
  protecting (MON-POW-NAT (M <= nat-times) *
		{ sort Nat.M -> Nat,
		  sort Nat.POWER -> Nat }
	      )
}

** Example 34
-- assume Example 11
-- reduce rest(put(e, st)) == st .  --> should be false.
-- reduce put(1 + 2, rest*(st, 0)) == put(3, st) . --> should be true

** Example 35
-- assume Example 11
-- bred rest(put(e,st)) . --> gives st
-- bred rest(put(e,st)) =b= st . --> gives true
-- bred rest(put(e,st)) == st . --> gives true
-- reduce rest(put(e,st)) =b= st . --> gives true .

** Example 36

open HSS-NAT-PROOF .
ops m n : -> Nat .
ops e e1 e2 : -> Elt .
ops st s1 s2 : -> Hss .
eq [hyp]: get rest*(s1, N) = get rest*(s2, N) .

start get s1 == get s2 .
apply -.p2 within term
apply .hyp within term
apply reduce at term  --> it should be true

reduce get rest*(put(e, s1), 0) == get rest*(put(e, e2), 0) .
reduce get rest*(put(e, s1), s(n)) == get rest*(put(e, e2), s(n)) .

start get rest*(rest s1, n) == get rest*(rest s2, n) .
apply -.p1 within term 
apply .hyp within term
apply reduce at term 

reduce get rest*(rest rest put(e1, (put(e2, st))), n) == get rest*(st,n) .
reduce get(rest*(rest*(put(e,st), s(m)), n)) == get(rest*(rest*(st, m), n)) .

--
eof
