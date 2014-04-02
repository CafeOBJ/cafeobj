-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Fri, 17 Jul 98 21:13:06 JST
-- Message-Id: <9807171213.AA13227@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  little fix of cat example
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 6146

-- Dear Toshimi,

-- I just fixed the problem of the constants in the cat proofs of the cat
-- example about compositions of natural transformations. I will change
-- the proof scores with apply when the new beta version is ready. At the
-- end I include the cat.mod file with these new small modifications.

-- BTW, I think I can notice the system under ACL really runs faster.

-- Best regards,
-- Razvan
-- ---------------------------------
-- basic code for categories
set auto context on

mod BASIC-CAT {

  [ Obj Arr ]

  op dom_ : Arr -> Obj 
  op cod_ : Arr -> Obj
    
  op 1 : Obj -> Arr
  op _;_ : ?Arr ?Arr -> ?Arr {assoc}

  var A  : Obj 
  var f  : Arr
  vars ?f ?g : ?Arr
  
  eq (f ; ?g) :is Arr = (?g :is Arr) and (dom ?g == cod f) .
  ceq dom(?f ; ?g) = dom ?f  if (?f ; ?g) :is Arr .
  ceq cod(?f ; ?g) = cod ?g  if (?f ; ?g) :is Arr .

  eq dom 1(A) = A .  eq cod 1(A) = A .
  ceq 1(A) ; f = f if dom f == A .
  ceq f ; 1(A) = f if cod f == A .
}

-- the theory of categories
mod* CATEGORY { using(BASIC-CAT) }

-- a category
mod! CAT1 { using(BASIC-CAT)
  ops 'f 'g 'e : -> Arr 
  ops 'A 'B 'C : -> Obj 
  eq dom 'f = 'A . eq cod 'f = 'B .
  eq dom 'g = 'A . eq cod 'g = 'B .
  eq dom 'e = 'B . eq cod 'e = 'C .
  eq 'f ; 'e = 'g ; 'e .
}
red 'f ; 1('B) ; 'e == 'g ; 'e ; 1('C) .
red 'f ; 'g .

mod! CAT2 {
  protecting(3TUPLE(NAT,INT,NAT))

  op _;_ : ?3Tuple ?3Tuple -> ?3Tuple

  vars s s' t t' : Nat
  vars a a' : Int
    
  cq << s ; a ; t >> ; << s' ; a' ; t' >> =  << s ; a + a' - (a * a') ; t' >>
     if t == s' .
}  
red << 1 ; 2 ; 2 >> ; << 2 ; 3 ; 3 >> .
red << 1 ; 2 ; 2 >> ; << 3 ; 3 ; 3 >> .
eof
red << 1 ; 2 ; 2 >> ; << 2 ; 0 ; 2 >> .

view cat2 from CATEGORY to CAT2 {
  sort Obj -> Nat,
  sort Arr -> 3Tuple,
  op 1(A:Obj) -> << A:Nat ; 0 ; A >>,
  op dom_ -> 1*_,
  op cod_ -> 3*_,
}    

mod* FUNCTOR (C :: CATEGORY, D :: CATEGORY) {

  op _fun : Obj.C -> Obj.D
  op _fun : Arr.C -> Arr.D

  vars f g : Arr.C 
  var A : Obj.C 
  
  eq dom(f fun) = (dom f) fun .
  eq cod(f fun) = (cod f) fun .
  eq 1(A) fun = 1(A fun) .
  ceq (f ; g) fun = (f fun) ; (g fun) if (f ; g) :is Arr . 
}

open FUNCTOR(CAT1,cat2) .
  ops n n' : -> Int .
  eq 'A fun = 1 .
  eq 'B fun = 2 .
  eq 'C fun = 3 .
  eq 'f fun = << 1 ; n  ; 2 >> .
  eq 'g fun = << 1 ; n' ; 2 >> .
  eq 'e fun = << 2 ; 1  ; 3 >> .
red ('f ; 'e) fun == ('g ; 'e) fun .
close

-- functors composition
mod* FUNCTOR-COMPOSE (C :: CATEGORY, D :: CATEGORY, E :: CATEGORY,
		      F :: FUNCTOR(C,D)*{op _fun -> _F},
		      G :: FUNCTOR(D,E)*{op _fun -> _G})
{
  op _fun : Obj.C -> Obj.E
  op _fun : Arr.C -> Arr.E 
    
  var A : Obj.C
  var f : ?Arr.C

  eq A fun = (A F) G .
  ceq f fun = (f F) G if f :is Arr .
}

-- composition of functors is a functor
open .
  op 'A :  -> Obj.C .
  ops 'f 'g :  -> Arr.C .
  eq dom('g) = cod('f) .
red 1('A) fun == 1('A fun) .
red ('f fun) ; ('g fun) == ('f ; 'g) fun .
close

-- identity functor
mod! ID-FUNCTOR (C :: CATEGORY) {
  protecting(FUNCTOR(C,C)*{op _fun -> _id})

  eq A:Obj id = A .
  eq f:Arr id = f .
}

mod* NAT-TRANSF (C :: CATEGORY, D :: CATEGORY,
		 F :: FUNCTOR(C,D)*{op _fun -> _F},
		 G :: FUNCTOR(C,D)*{op _fun -> _G})
{
  op _nt : Obj.C -> Arr.D

  vars A B : Obj.C
  var f : Arr.C

  eq dom(A nt) = A F .
  eq cod(A nt) = A G .

  cq [nat-compo]: (A nt) ; (f G) = (f F) ; (B nt)
     if (A == dom f) and (B == cod f) .
}

-- natural transformation composition
mod* NAT-TRANSF-COMPOSE (C   :: CATEGORY, D :: CATEGORY,
			 F   :: FUNCTOR(C,D)*{op _fun -> _F},
		         G   :: FUNCTOR(C,D)*{op _fun -> _G},
			 H   :: FUNCTOR(C,D)*{op _fun -> _H},
			 NT1 :: NAT-TRANSF(C,
					   D,
					   F,
					   G)*
			 {op _nt -> _nt1},
			 NT2 :: NAT-TRANSF(C,
					   D,
					   G{op _F -> _G},
					   H{op _G -> _H})*
			 {op _nt -> _nt2})
{
  op _nt : Obj.C -> Arr.D

  var A : Obj.C

  eq (A nt) = (A nt1) ; (A nt2) .
}

-- composition of natural transformations is a natural transformation
open .
  ops 'A 'B : -> Obj.C .
  op 'f : -> Arr.C .
eq dom 'f = 'A .
eq cod 'f = 'B .
-- prove commutativity of inner left square
start ('A nt1);('f G) == ('f F);('B nt1) .
apply NT1.nat-compo with B = 'B within term
apply reduce at term -- condition
apply reduce at term
eq ('A nt1) ; ('f G) = ('f F) ; ('B nt1) .
-- prove commutativity of inner right square
start ('A nt2) ; ('f H) == ('f G) ; ('B nt2) .
apply NT2.nat-compo with B = 'B within term
apply reduce at term -- condition
apply reduce at term
eq ('A nt2 ) ; ('f H) = ('f G) ; ('B nt2) .
-- prove outer rectangle is commutative
red ('A nt) ; ('f H) == ('f F) ; ('B nt) .
close

mod* NT-FUNCTOR-COMPOSE (C :: CATEGORY, D :: CATEGORY, E :: CATEGORY,
			 F  :: FUNCTOR(C,D)*{op _fun -> _F},
		         G  :: FUNCTOR(C,D)*{op _fun -> _G},
			 H  :: FUNCTOR(D,E)*{op _fun -> _H},
			 NT :: NAT-TRANSF(C,
					  D,
					  F,
					  G))
{
  op _nt' : Obj.C -> Arr.E

  var A : Obj.C

  eq (A nt') = (A nt) H .
}
-- horizontal composition between a natural transformation and a functor
-- is a natural transformation
open .
  ops  'A 'B : -> Obj.C .
  op 'f : -> Arr.C .
eq dom 'f = 'A .
eq cod 'f = 'B .
-- red ('A nt') ; (('f F) H) == (('f G) H) ; ('B nt') .
close

mod* FUNCTOR-NT-COMPOSE (C :: CATEGORY, D :: CATEGORY, E :: CATEGORY,
			 F  :: FUNCTOR(C,D)*{op _fun -> _F},
		         G  :: FUNCTOR(C,D)*{op _fun -> _G},
			 H  :: FUNCTOR(E,C)*{op _fun -> _H},
			 NT :: NAT-TRANSF(C,
					  D,
					  F,
					  G))
{
  op _nt' : Obj.E -> Arr.D

  var A : Obj.E

  eq (A nt') = (A H) nt .
}
-- horizontal composition between a functor and a natural trasnformation 
-- is a natural transformation
open .
  ops 'A 'B : -> Obj.E .
  op 'f : -> Arr.E .
eq dom 'f = 'A .
eq cod 'f = 'B .
red ('A nt') ; (('f H) F) == (('f H) G) ; ('B nt') .
close

mod* ADJUNCTION
     ( C   :: CATEGORY,
       D   :: CATEGORY,
       F   :: FUNCTOR(C,D)*{op _fun -> _F},
       U   :: FUNCTOR(D,C)*{op _fun -> _U},
       ETA :: NAT-TRANSF(C,
			 C,
			 ID-FUNCTOR(C){op _F -> _id},
			 FUNCTOR-COMPOSE(C,
					 D,
					 C,
					 F{op _F -> _F},
					 U{sort Arr.E -> Arr.C,
					   sort Obj.E -> Obj.C,
					   op _G -> _U})
			 {op _G -> _fun}
			 )
       *{op _nt -> _eta},
       EPS :: NAT-TRANSF(D,
			 D,
			 FUNCTOR-COMPOSE(D,
					 C,
					 D,
					 U{op _F -> _U},
					 F{sort Arr.E -> Arr.D,
					   sort Obj.E -> Obj.D,
					   op _G -> _F})
			 {op _F -> _fun},
			 ID-FUNCTOR(D){op _G -> _id})
       *{op _nt -> _eps} )
{
  var c : Obj.C
  var d : Obj.D
 -- triangular laws:
 eq (c eta F) ; (c F eps) = 1(c F) .
 eq (d U eta) ; (d eps U) = 1(d U) .
}    

-- proof that the composition of two adjunctions is an adjunction

