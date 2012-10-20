-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Wed, 10 Jun 98 10:08:01 JST
-- Message-Id: <9806100108.AA08393@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  cat example 
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 3137

-- Dear Toshimi,

-- Thanks for the latest patches. I think we advance with this example. I
-- am also looking forward for the new patches.

-- I am sending you the latest version of this example. You might try to
-- run it and see what are still the current problem at this stage. The
-- first part runs well now.

-- Best regards,
-- Razvan

-- PS. I put 2 versions of the natural transformation not because I want
-- both of them to work, but at least one of them should maybe
-- work. Please feel also free to modify this code and send it back to
-- me, if you think it is necessary. 
-- --------------------------------------------------------------
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
red in CAT1 : 'f ; 1('B) ; 'e == 'g ; 'e ; 1('C) .
red in CAT1 : 'f ; 'g .

mod! CAT2 {
  protecting(3TUPLE(NAT,INT,NAT))

  op _;_ : ?3Tuple ?3Tuple -> ?3Tuple

  vars s s' t t' : Nat
  vars a a' : Int
    
  cq << s ; a ; t >> ; << s' ; a' ; t' >> =  << s ; a + a' - (a * a') ; t' >>
     if t == s' .
}  
red in CAT2 : << 1 ; 2 ; 2 >> ; << 2 ; 3 ; 3 >> .
red in CAT2 : << 1 ; 2 ; 2 >> ; << 3 ; 3 ; 3 >> .
red in CAT2 : << 1 ; 2 ; 2 >> ; << 2 ; 0 ; 2 >> .

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

-- mod* NAT-TRANSF (C :: CATEGORY, D :: CATEGORY,
--                  F :: FUNCTOR(C,D)*{op _fun -> _fun.F},
-- 		 G :: FUNCTOR(C,D)*{op _fun -> _fun.G})
-- {
--   op _nt : Obj.C -> Arr.D

--   vars A B : Obj.C
--   vars f g : Arr.C

--   eq dom(A nt) = A fun.F .
--   eq cod(A nt) = A fun.G .

--   cq (A nt) ; (f fun.G) = (f fun.F) ; (B nt)
--     if (A == dom f) and (B == cod f) .
-- }

-- eof

mod* NAT-TRANSF (C :: CATEGORY, D :: CATEGORY,
		 F :: FUNCTOR(C, D), G :: FUNCTOR(C, D))
{
  op _nt : Obj.C -> Arr.D

  vars A B : Obj.C
  vars f g : Arr.C

  eq dom(A nt) = A fun.F .
  eq cod(A nt) = A fun.G .

  cq (A nt) ; (f fun.G) = (f fun.F) ; (B nt)
    if (A == dom f) and (B == cod f) .
}

eof

mod* NAT-TRANSF (F :: FUNCTOR(C,D), G :: FUNCTOR(C,D)) {
  op _nt : Obj.C -> Arr.D

  vars A B : Obj.C
  vars f g : Arr.C

  eq dom(A nt) = A fun.F .
  eq cod(A nt) = A fun.G .

  cq (A nt) ; (f fun.G) = (f fun.F) ; (B nt)
    if (A == dom f) and (B == cod f) .
}

mod* ADJUNCTION {
-- triangular laws
}

-- proof that the composition of two adjunctions is an adjunction




