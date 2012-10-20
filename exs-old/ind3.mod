** -*- Mode:CafeOBJ -*-
**> this is file: exs/ind3.module translated from ~goguen/obj/exs/ind3.obj
**> not yet translated complately. does not work now.
**> induction in OBJ

**> *************** SETUP *****************

module! NAT' {
  [ Nat ]
  op 0 : -> Nat 
  op s_ : Nat -> Nat 
  op add : Nat Nat -> Nat 
  vars N M : Nat 
  eq add(0,N) = N .
  eq add(s N,M) = s add(N,M).
  ops x y z : -> Nat 
}

module* NATF0
     principal-sort Nat
{
  extending (NAT')
  op a : -> Nat 
}

module! SETUP(A :: NATF0){
  extending (NAT')
  -- let t1 = add(a,add(y,z)) . 
  -- let t2 = add(add(a,y),z) .
  -- let e  = t1 == t2 .

  ops t1 t2 : -> Nat
  op e : -> Bool
  eq t1 = add(a,add(y,z)) . 
  eq t2 = add(add(a,y),z) .
  eq e  = t1 == t2 .
}

set trace whole on .

**> *************** BASE *****************

make ADD-ASSOC-B (
 (SETUP *{ op e -> base })[NAT'{op a -> 0}]
)

select ADD-ASSOC-B
show .
red base .

**> *************** STEP *****************

-- set sys universal-sort on

module! HYP {
  using (SETUP[NAT'{ op a -> x }])
  op eq : *Universal* *Universal* -> Bool 
  eq eq(X:*Universal*, Y:*Universal*) = X == Y .
  eq t1 = t2 .
}

select HYP
show .
red eq(add(x,add(y,z)),add(add(x,y),z)) .

module! STEP {
  using ((SETUP *{ op e -> step })
	 [NAT { op a -> s x } ])
  protecting (HYP)
}

show .
red step .

**> *************** BOTH *****************

** obj HYP is using SETUP[(x).NAT] .
**   eq t1 = t2 .
** endo

** show .

module! STEP {
  using ((SETUP *{ op e -> base })[NAT'{ op a -> 0 }])
  using ((SETUP *{ op e -> step })[NAT'{ op a -> s x }])
  protecting (HYP)
}

show .
red base and step .

**> *************** MAKE *****************

**> this one does not work:

make STEP (
  (SETUP * { op e -> step}) [NAT { op a -> s x }]
  + HYP 
}

show .
red step .

--
-- set sys universal-sort off
--
eof
**
$Id: ind3.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $

