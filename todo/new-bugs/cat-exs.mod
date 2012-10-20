-- Date: Sun, 28 Jun 1998 23:24:53 +0300
-- From: Diaconescu Razvan <diacon@stoilow.imar.ro>
-- Message-Id: <9806282024.AA01304@stoilow.imar.ro>
-- To: sawada@sra.co.jp
-- Subject:  progress on parameters
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 5369

-- Dear Toshimi,

-- Now I am trying to move forward with the category theory example,
-- which provides an good benchmark for fixing the parameterization
-- implemtnation for our language. I insert my latest code at the end of
-- this message. Please try to run it and see what are the current
-- problems. We are pretty close to the original plan, i.e., to specify
-- adjunctions and prove that composition of adjunctions is still and
-- adjunction, so modulo fixing the current problems this example will not
-- be developed much more. But there are several important points to
-- tackle with our implementation. 

-- Before you see it by yourself I would like to point out some important
-- issues with respect to the current version of this example.

-- 1. At this stage I think it became obvious that qualifying of
-- operations is very useful for smooth elegant specification. In some
-- situations it seems to me is very necessary (you will see by running
-- this code).

-- 2. There is a problem related to the partiality which prevents the
-- correct execution of the verification that the composite of two
-- functors is still a functor

-- red ('f fun) ; ('g fun) == ('f ; 'g) fun .

-- How can we make this work properly?

-- 3. The final module (ADJUNCTION) has several problems, some of them
-- maybe related to 1. I didnt attempt to rearrange it in order to run it
-- with the current system because I wanted to provide a simple clean
-- benchmark of what should be achieved.

-- 4. As implementation of parameters develops we should try to simplify
-- the code and slowly get rid off some things which are now there only
-- in order to make things work (such as renaming in the
-- parameters). Please try to modify the code by yourself as you think is
-- better and let me know.

-- Best regards,
-- Razvan
-- ---------------------------------------------------------------------
set auto context on

-- basic code for categories
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

-- -- functor composition
-- mod* FUNCTOR-COMPOSE (C :: CATEGORY, D :: CATEGORY, E :: CATEGORY,
-- 		      F :: FUNCTOR(C,D)*{op _fun -> _F},
-- 		      G :: FUNCTOR(D,E)*{op _fun -> _G})
-- {
--   op _fun : Obj.C -> Obj.E
--   op _fun : Arr.C -> Arr.E 
--   -- op _fun : ?Arr.C -> ?Arr.E  -- (1) redundant? provided anyway by the system?
    
--   var A : Obj.C
--   var f : Arr.C

--   eq A fun = (A F) G .
-- --  eq (f fun) : Arr = (f : Arr) .
-- --  in full MEL the following should work unconditional
--   ceq f fun = (f F) G if f :is Arr . -- (2) 
-- }
-- -- composition of functors is a functor
-- open .
--   op 'A :  -> Obj.C .
--   ops 'f 'g :  -> Arr.C .
--   eq dom('g) = cod('f) .
-- red 1('A) fun == 1('A fun) .
-- red ('f fun) ; ('g fun) == ('f ; 'g) fun .
-- close
set mel sort on
-- set mel always on
-- set mel reduce on
set auto context on

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
  vars f g : Arr.C

  eq dom(A nt) = A F .
  eq cod(A nt) = A G .

  cq (A nt) ; (f G) = (f F) ; (B nt)
    if (A == dom f) and (B == cod f) .
}

-- mod* ADJUNCTION
--  (C   :: CATEGORY,
--   D   :: CATEGORY,
--   F   :: FUNCTOR(C,D)*{op _fun -> _F},
--   U   :: FUNCTOR(D,C)*{op _fun -> _U},
--   ETA :: NAT-TRANSF(C,C, ID-FUNCTOR(C), FUNCTOR-COMPOSE(C,D,C,F,U))
-- 		  *{op _nt -> _eta},
--   EPS :: NAT-TRANSF(D,D, FUNCTOR-COMPOSE(D,C,D,U,F), ID-FUNCTOR(D))
-- 		  *{op _nt -> _eps})
-- {
--   var c : Obj.C
--   var d : Obj.D
-- -- triangular laws:
--   eq (c eta F) ; (c F eps) = 1(c F) .
--   eq (d U eta) ; (d eps U) = 1(d U) .
-- }    

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
