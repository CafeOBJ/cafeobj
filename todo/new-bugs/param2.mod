-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Tue, 9 Jun 98 14:08:04 JST
-- Message-Id: <9806090508.AA08143@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  parameterization of partial operations 
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 2648

-- Dear Toshimi,

-- I am struggling with developing a category theory example, at the end
-- I have grand plans about this since it would involve non-trivial
-- parameterization in conjunction with partial operations.

-- But I have some problems. Look at this code and run:

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
  
  eq (f ; ?g) : Arr = (?g : Arr) and (dom ?g == cod f) .
  ceq dom(?f ; ?g) = dom ?f  if (?f ; ?g) : Arr .
  ceq cod(?f ; ?g) = cod ?g  if (?f ; ?g) : Arr .

  eq dom 1(A) = A .  eq cod 1(A) = A .
  ceq 1(A) ; f = f if dom f == A .
  ceq f ; 1(A) = f if cod f == A .
}

-- the theory of categories
mod* CATEGORY { pr(BASIC-CAT) }

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
  sort ?Arr -> ?3Tuple,
  op 1(A:Obj) -> << A:Nat ; 0 ; A >>,
  op dom_ -> 1*_,
  op cod_ -> 3*_,
  op _;_ -> _;_
}    

-- This gives

-- [Warning]: redefining view cat2 
-- Error: Caught fatal error [memory may be damaged]
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by CAFEOBJ-EVAL-VIEW-PROC.
-- Broken at DECLARE-VIEW.  Type :H for Help.

-- Ideally if we have a mapping such that Arr -> 3Tuple then ?Arr should
-- be mapped by default to ?3Tuple. Lets try this:

view cat2 from CATEGORY to CAT2 {
   sort Obj -> Nat,
   sort Arr -> 3Tuple,
   op 1(A:Obj) -> << A:Nat ; 0 ; A >>,
   op dom_ -> 1*_,
   op cod_ -> 3*_,
   op _;_ -> _;_
} 

-- -- defining view cat2 
-- [Warning]: redefining view cat2 
-- [Error]: Operator mapping is not injective, the declaration
--          _;_ : ?Arr ?Arr -> ?Arr
--          has no proper image in the target.

-- In fact, the last line of the view should be redundant (since this
-- mapping should be done by default), isnt it? Lets try it

view cat2 from CATEGORY to CAT2 {
  sort Obj -> Nat,
  sort Arr -> 3Tuple,
  op 1(A:Obj) -> << A:Nat ; 0 ; A >>,
  op dom_ -> 1*_,
  op cod_ -> 3*_,
}    

-- -- defining view cat2 
-- [Warning]: redefining view cat2 
-- [Warning]: view incomplete for operator _;_ : ?Arr ?Arr -> ?Arr of CATEGORIES
--            view to CAT2
--            !! MAY CAUSE PANIC LATER !! done.

-- So, none of these variants works. Ideally, the specifier should write
-- the last one by using the simple default for the unspecified part of
-- the view.

-- Best regards,
-- Razvan


