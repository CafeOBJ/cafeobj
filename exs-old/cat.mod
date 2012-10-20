** -*- Mode:CafeOBJ -*-
-- from `cat.obj' of obj3 example
--
require simple-set ./simple-set

** theory of categories

module* CAT-TH
{
  signature {
    -- arrow (Morphism) and Object
    [ Mor Obj ]
    -- source & target of arrows
    ops (d0_) (d1_) : Mor -> Obj
    -- arrow composition
    op _;_ : Mor Mor -> Mor { associative }
    -- identity arrow
    op id_ : Obj -> Mor 
  }
  axioms {
    var O : Obj 
    vars M M0 M1 : Mor
    -- ------------------
    eq d0 id O = O .
    eq d1 id O = O .
    eq d0 (M0 ; M1) = d0 M0 .
    eq d1 (M0 ; M1) = d1 M1 .
    eq (id d0 M); M = M .
    eq M ; id d1 M = M .
  }
}

** generic category of sets
module! CAT-SET(X :: TRIV)
{
  protecting (SET[X])
  signature {
    [ Fn ]
    ops (d0_) (d1_) : Fn -> Set 
    op _;_ : Fn Fn -> Fn { associative }
    op id_ : Set -> Fn 
    op _of_ : Fn Elt -> Elt
  }
  axioms {
    var O : Set 
    vars F F0 F1 : Fn 
    var E : Elt 
    -- --------------------------
    eq d0 id O = O .
    eq d1 id O = O .
    eq d0 (F0 ; F1) = d0 F0 .
    eq d1 (F0 ; F1) = d1 F1 .
    eq (id d0 F) ; F = F .
    eq F ; id d1 F = F .
    eq (F0 ; F1) of E = F0 of (F1 of E) .
    eq (id O) of E = E .
  }
}

** CAT-SET always gives a category
view CAT-SET-AS-CAT from CAT-TH to CAT-SET
{
  sort Obj -> Set,
  sort Mor -> Fn 
}

** 2-cones in Category C
module! CO2CONE(C :: CAT-TH)
{
  protecting (2TUPLE(C1 <= C { sort Elt -> Obj },
		     C2 <= C { sort Elt -> Obj })
	      * { sort 2Tuple -> Base })
  signature {
    [ Co2cone ]
    op cone : Mor Mor -> Co2cone
    ops j1 j2 : Co2cone -> Mor
    op apex : Co2cone -> Obj
    op base : Co2cone -> Base 
  }
  axioms {
    vars M1 M2 : Mor
    -- -----------------------------------------
    eq j1(cone(M1,M2)) = M1 .
    eq j2(cone(M1,M2)) = M2 .
    eq apex(cone(M1,M2)) = d1 M1 .
    eq base(cone(M1,M2)) = << d0 M1 ; d0 M2 >> .
  }
}

** theory of coproduct in C
module* CO2PROD-TH(C :: CAT-TH)
{
  protecting (CO2CONE[C])
  signature {
    [ Uco2cone < Co2cone ]           ** a very nice subsort!
    op ucone : Obj Obj -> Uco2cone   ** coproduct cone
    op _++_ : Obj Obj -> Obj         ** coproduct object
    op umor : Uco2cone Co2cone -> Mor
  }
  axioms {
    vars A B : Obj 
    vars F G H : Mor
    -- --------------------------------------------------------
    eq apex(ucone(A,B)) = A ++ B .
    eq base(ucone(A,B)) = << A ; B >> .
    eq (j1(ucone(A,B))); umor(ucone(A,B),cone(F,G)) = F .
    eq (j2(ucone(A,B))); umor(ucone(A,B),cone(F,G)) = G .
    cq H = umor(ucone(A,B),cone(F,G))
       if (j1(ucone(A,B)); H == F) and (j2(ucone(A,B)); H == G) .
  }
}

** theory of injections for building a coproduct
module* 2INJ-TH
{
  signature {
    [ Elt ]
    ops i0 i1 i0inv i1inv : Elt -> Elt 
    ops i0pred i1pred : Elt -> Bool 
  }
  axioms {
    var E : Elt 
    -- -----------------------------------
    eq i0inv(i0(E)) = E .
    eq i1inv(i1(E)) = E .
    eq i0pred(i0(E)) = true .
    eq i0pred(i1(E)) = false . 
    eq i1pred(i1(E)) = true .
    eq i1pred(i0(E)) = false .
  }
}

** coproduct in a category of sets, given injections for it
module! CO2PROD-CAT-SET(J :: 2INJ-TH)
{
  extending (CO2CONE(CAT-SET(J){ sort Obj -> Set 
				 sort Mor -> Fn }))
  signature {
    [ Uco2cone < Co2cone ]
    op ucone : Set Set -> Uco2cone 
    op umor : Uco2cone Co2cone -> Fn
    ops I0 I1 : Set -> Set
    op _++_ : Set Set -> Set
  }
  axioms {
    vars A B : Set 
    vars F G : Fn 
    var E : Elt 
    var ES : EltSeq
    -- ----------------------------------------
    eq I0({}) = {} .
    eq I0({ E, ES }) = { i0(E) } U I0({ ES }) .
    eq I1({}) = {} .
    eq I1({ E, ES }) = { i1(E) } U I1({ ES }) .
    eq A ++ B = I0(A) U I1(B) .
    eq apex(ucone(A,B)) = A ++ B .
    eq base(ucone(A,B)) = << A ; B >> .
    cq j1(ucone(A,B)) of E = i0(E) if E in A .
    cq j2(ucone(A,B)) of E = i1(E) if E in B .
    cq umor(ucone(A,B),cone(F,G)) of E = F of i0inv(E) if i0pred(E) .
    cq umor(ucone(A,B),cone(F,G)) of E = G of i1inv(E) if i1pred(E) .
  }

}

** CO2PROD-CAT-SET gives a coproduct
** view CO2PROD-CAT-SET-AS-CO2PROD-TH[J :: 2INJ-TH] 
**    from CO2PROD-TH[CAT-SET[J]] to CO2PROD-CAT-SET[J] endv
** don't have parameterized views yet

** constructions for the category of sets of integers
make CAT-SET-INT (CAT-SET[INT])

** coproduct in the category of sets of integers
make CO2PROD-CAT-SET-INT
(CO2PROD-CAT-SET[INT{ sort Elt -> Int
		      var I : Elt
		      op i0(I) -> (2 * I), 
		      op i0inv(I) -> (I quo 2),
		      op i0pred(I) -> (I rem 2 == 0),
		      op i1(I) -> 1 + (2 * I),
		      op i1inv(I) -> ((I - 1) quo 2),
		      op i1pred(I) -> (I rem 2 == 1) }
		 ]
)

** this says the above really is a coproduct
view CO2PROD-CAT-SET-INT-VIEW
     from CO2PROD-TH[CAT-SET(INT){ sort Obj -> Set 
				   sort Mor -> Fn }
		      ]
     to CO2PROD-CAT-SET-INT
{
}

** note the view within view and empty body of outermost view

** some test cases
mod! CO2PROD-TEST
{
  protecting (CO2PROD-CAT-SET-INT)
  signature {
    ops s1 s2 s3 s4 : -> Set }
  axioms {
    eq s1 = { 1 } .
    eq s2 = s1 U { 2 } .
    eq s3 = s2 U { 3 } .
    eq s4 = { 2 } U { 3 } .
  }
  signature {
    op g : -> Fn 
  }
  axioms {
    eq g of 3 = 2 .
    eq g of 2 = 1 .
    eq d0 g = s4 .
    eq d1 g = s3 .
  }
}

select CO2PROD-TEST
reduce base(ucone(s1,s1)) .                         **> should be: <<{1};{1}>>
reduce apex(ucone(s1,s1)) .                         **> should be: {2,3}
reduce umor(ucone(s1,s1),cone(id s1,id s1)) of 2 .  **> should be: 1
reduce umor(ucone(s1,s1),cone(id s1,id s1)) of 3 .  **> should be: 1

reduce base(ucone(s2,s3)) .                      **> should be: <<{1,2};{1,2,3}>>
reduce apex(ucone(s2,s3)) .                      **> should be: {2,4,3,5,7}
reduce umor(ucone(s2,s3),cone(id s2,id s3)) of 2 .  **> should be: 1
reduce umor(ucone(s2,s3),cone(id s2,id s3)) of 4 .  **> should be: 2
reduce umor(ucone(s2,s3),cone(id s2,id s3)) of 3 .  **> should be: 1
reduce umor(ucone(s2,s3),cone(id s2,id s3)) of 5 .  **> should be: 2
reduce umor(ucone(s2,s3),cone(id s2,id s3)) of 7 .  **> should be: 3

reduce base(ucone(s4 ,s3)) .                     **> should be: <<{2,3};{1,2,3}>>
reduce apex(ucone(s4,s3)) .                      **> should be: {4,6,3,5,7}
reduce umor(ucone(s4,s3),cone(g,id s3)) of 4 .   **> should be: 1
reduce umor(ucone(s4,s3),cone(g,id s3)) of 6 .   **> should be: 2
reduce umor(ucone(s4,s3),cone(g,id s3)) of 3 .   **> should be: 1
reduce umor(ucone(s4,s3),cone(g,id s3)) of 5 .   **> should be: 2
reduce umor(ucone(s4,s3),cone(g,id s3)) of 7 .   **> should be: 3
--
eof
**
$Id: cat.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
