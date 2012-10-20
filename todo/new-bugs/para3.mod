-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Tue, 9 Jun 98 20:58:42 JST
-- Message-Id: <9806091158.AA08299@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  parameterized paramters
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 2240

-- Dear Toshimi,

-- Now here is a very interesting issue. The encoding of natural
-- transformations in CafeOBJ makes essential use of paramteterized
-- parameters. I think this does not work well yet.

-- Look at the following specification:

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
-- mod* CATEGORY { pr(BASIC-CAT) }
mod* CATEGORY { us(BASIC-CAT) }

mod* FUNCTOR (C :: CATEGORY, D :: CATEGORY) {

  op _fun : Obj.C -> Obj.D
  op _fun : Arr.C -> Arr.D

  vars f g : Arr.C 
  var A : Obj.C 
  
  eq dom(f fun) = (dom f) fun .
  eq cod(f fun) = (cod f) fun .
  eq 1(A) fun = 1(A fun) .
  ceq (f ; g) fun = (f fun) ; (g fun) if (f ; g) : Arr . 
}

mod* NAT-TRANSF (F :: FUNCTOR, G :: FUNCTOR) {
  op _nt : Obj.C.F -> Arr.D.G

  var A : Obj.C.F 

  eq dom(A nt) = A fun .
  eq cod(A nt) = A fun .
}

mod* NAT-TRANSF' (C :: CATEGORY, D :: CATEGORY,
		 F :: FUNCTOR(C,D), G :: FUNCTOR(C,D))
{
  op _nt : Obj.C.F -> Arr.D.G

  var A : Obj.C.F 

  eq dom(A nt) = A fun .
  eq cod(A nt) = A fun .
}


-- -- defining module* NAT-TRANSF
-- [Warning]: redefining module NAT-TRANSF _*_*_*_*_*_*._*_*_*_*_*_*.
-- [Error]: module name C is ambiguous in the current context.
-- -- failed to evaluate the form:
-- Operator declaration:
--      symbol = (_ nt)
--      arity = Obj.C
--      coarity = Arr.D
-- attributes : 


mod* NAT-TRANSF' (F :: FUN(C,D), G :: FUN(C,D)) {
  op _nt : Obj.C -> Arr.D

  var A : Obj.C  

  eq dom(A nt) = A fun.F .
  eq cod(A nt) = A fun.G .
}

eof
--

[Error]: Cannot evaluate module in view: view target = C
-- could not evaluate instantiation: FUNCTOR(C <= C, D <= D)
-- failed to evaluate the form:
import declaration : mode = protecting, module = FUNCTOR(C <= C, 
   D <= D)

I think you can undersand my intention. We have here two functors
F,G : C -> D, and then a natural transformation nt : F -> G.
I think it is natural to use such kind of parameters. Is this
something to be improved in the implementation (a kind of bug), or
there is another writing style in which to achieve this intention? 

Thanks,
Razvan

