-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Tue, 9 Jun 98 17:52:57 JST
-- Message-Id: <9806090852.AA08226@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  new problems with cat example
-- Content-Type: text
-- Content-Length: 3317

-- Toshimi,

-- Thank you for the prompt fixing of the previous problem. Now I see
-- another problem.

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
  
  eq (f ; ?g):is Arr = (?g :is Arr) and (dom ?g == cod f) .
  ceq dom(?f ; ?g) = dom ?f  if (?f ; ?g):is Arr .
  ceq cod(?f ; ?g) = cod ?g  if (?f ; ?g):is Arr .

  eq dom 1(A) = A .  eq cod 1(A) = A .
  ceq 1(A) ; f = f if dom f == A .
  ceq f ; 1(A) = f if cod f == A .
}

-- the theory of categories
-- mod* CATEGORY { pr(BASIC-CAT) }
mod* CATEGORY { us(BASIC-CAT) }

-- a category
mod! CAT1 { pr(BASIC-CAT)
  ops 'f 'g 'e : -> Arr 
  ops 'A 'B 'C : -> Obj 
  eq dom 'f = 'A . eq cod 'f = 'B .
  eq dom 'g = 'A . eq cod 'g = 'B .
  eq dom 'e = 'B . eq cod 'e = 'C .
  eq 'f ; 'e = 'g ; 'e .
}

mod! CAT2 {
  protecting(3TUPLE(NAT,INT,NAT))

  op _;_ : ?3Tuple ?3Tuple -> ?3Tuple

  vars s s' t t' : Nat
  vars a a' : Int
    
  cq << s ; a ; t >> ; << s' ; a' ; t' >> =  << s ; a + a' - (a * a') ; t' >>
     if t == s' .
}  

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
  ceq (f ; g) fun = (f fun) ; (g fun) if (f ; g):is Arr.C . 
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

eof
-- close

This gives the following:

-- opening module FUNCTOR(C <= CAT1, D <= cat2).. done._
[Error] no parse for axiom (ignored): 
 No possible parse for LHS
- possible RHS
  
  1:NzNat
          
  

** returning to top level
%FUNCTOR(C <= CAT1, D <= cat2)> parse 'A .
'A : Obj
%FUNCTOR(C <= CAT1, D <= cat2)> parse 'A fun .
[Error] no successfull parse
  
  parsed:[_],rest:[_]:SyntaxErr    
         /              \           
      'A:Obj  ("fun"):_ Universal _
                                    
  
(parsed:[ 'A ], rest:[ ("fun") ]) : SyntaxErr
%FUNCTOR(C <= CAT1, D <= cat2)> show .
*
module FUNCTOR(C <= CAT1, D <= cat2)
{ ** opening
  imports {
    protecting (CAT1)
    protecting (CAT2)
  }
  signature {
    op _ fun : 3Tuple -> 3Tuple { prec: 41 }
    op _ fun : 3Tuple -> 3Tuple { prec: 41 }
    op n : -> Int
    op n' : -> Int
  }
  axioms {
    eq 1* (f:3Tuple fun) = 1* f:3Tuple fun .
    eq 3* (f:3Tuple fun) = 3* f:3Tuple fun .
    eq << A:Nat ; 0 ; A:Nat >> fun = << (A:Nat fun) ; 0 ; (A:Nat 
        fun) >> .
    ceq (f:3Tuple ; g:3Tuple) fun = (f:3Tuple fun) ; (g:3Tuple fun
        ) if f:3Tuple ; g:3Tuple : 3Tuple .
  }
}
%FUNCTOR(C <= CAT1, D <= cat2)> 

I think there is a problem with respect to this instantiation. For
example 'A fun does not parse which mught be explained by the rather
strange look of the instantiated module. I dont see any operation  for
fun on objects (but the one for fun on arrows is duplicated). Also the
3rd equation seems strange to me.

Best regards,
Razvan

