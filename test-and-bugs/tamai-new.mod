--
-- 
-- 
module LATTICE
{
  signature {
    [ Elt ]
    op _v_ : Elt Elt -> Elt { assoc comm }
    op _^_ : Elt Elt -> Elt { assoc comm }

    pred _<=_ : Elt Elt
  }

  axioms {
    vars x y : Elt
    eq x v (x ^ y) = x .
    eq x ^ (x v y) = x .
    eq x <= y = x ^ y == x .
  }
}

module LATTICE-T 
{
  protecting (LATTICE)

  signature {
    op top : -> Elt
  }

  axioms {
    var x : Elt
    eq top ^ x = x .
    -- prove "x <= top == true" (should be trivial)
  }
}

module TRANS (lt :: LATTICE-T)
{
  [ Trans ]
  signature {
    op _*_ : Trans Trans -> Trans { assoc }
    op _^_ : Trans Trans -> Trans { assoc comm }
    op _<_> : Trans Elt -> Elt
    ops iota tau : -> Trans
  }
  axioms {
    vars f f1 f2 : Trans
    vars x y : Elt
    eq (f1 * f2) < x > = f1 < (f2 < x >) > .
    eq (f1 ^ f2) < x > = (f1 < x >) ^ (f2 < x >) .
    eq iota < x > = x .
    eq tau < x > = top .
    eq (not(x <= y)) or ((f < x >) <= (f < y >)) = true .
  }
}

module GRAPH 
{
  [ Vertex Edge ]
  signature {
    ops head tail : Edge -> Vertex
  }
}

module LIST (X :: TRIV)
{
  [ Elt < List ]
  signature {
    op nil : -> List
    op __ : List List -> List { assoc idr: nil }
  }
}

module GRAPHEX
{
  imports {
    protecting (GRAPH)
    protecting (LIST(X <= view to GRAPH { sort Elt -> Vertex })
		* { sort List -> Vlist })
    protecting (LIST(X <= view to GRAPH { sort Elt -> Edge })
		* { sort List -> Elist })
  }
  
  signature {
    op source : -> Vertex
    op inedge : Vertex -> Elist
    op outedgt : Vertex -> Elist
  }
}

module MEETOVERLIST (L :: LATTICE-T)
{
  protecting (LIST(X <= L) * { sort List -> Llist })
  signature {
    op meet : Llist -> Elt
  }

  axioms {
    var e : Elt
    var el : Llist
    eq meet(nil) = top .
    eq meet(e el) = e ^ meet(el) .
  }
}

module FIXEDPOINT (G :: GRAPHEX, L :: LATTICE-T)
{
  protecting (TRANS(L))
  protecting (MEETOVERLIST(L))
  signature {
    op fe : Edge -> Trans
    op xv : Vertex -> Elt
    op mapfe : Elist Vertex -> Llist
    op bs : -> Elt
  }
  axioms {
    var v : Vertex
    var e : Edge
    var el : Elist
    eq mapfe(nil, v) = (nil):Llist .
    eq mapfe((e el), v) = (fe(e) < xv(v) >) mapfe(el, v) .
    eq xv(source) = bs .
    eq xv(v) = meet(mapfe(inedge(v), v)) .
  }
}

module NAT-MAXMIN
{
  protecting (NAT)
  signature {
    [ Nat < Nat+ ]
    op inf : -> Nat+
    ops min max : Nat+ Nat+ -> Nat+ { assoc comm }
    pred _<=_ : Nat+ Nat+
    op _+_ : Nat+ Nat+ -> Nat+ { assoc comm }
  }
  axioms {
    vars x y : Nat+
    eq x <= inf = true .
    eq x + inf = inf .
    ceq min(x,y) = x if x <= y .
    ceq min(x,y) = y if y <= x .
    ceq max(x,y) = x if y <= x .
    ceq max(x,y) = y if x <= y .
  }
}

view LATTICEtoNAT from LATTICE-T to NAT-MAXMIN
{
  sort Elt -> Nat+,
  op _^_ -> min,
  op _v_ -> max,
  op top -> inf,
  op _<=_ -> _<=_
}


module GRAPH-A
{
  [ Vertex Edge ]
  signature {
    ops v1 v2 v3 v4 v5 v6 : -> Vertex
    ops e1 e2 e3 e4 e5 e6 e7 e8 e9 : -> Edge
    ops head tail : Edge -> Vertex
  }
  axioms {
    eq head(e1) = v1 . eq tail(e1) = v2 .
    eq head(e2) = v1 . eq tail(e2) = v3 .
    eq head(e3) = v2 . eq tail(e3) = v4 .
    eq head(e4) = v2 . eq tail(e4) = v5 .
    eq head(e5) = v3 . eq tail(e5) = v4 .
    eq head(e6) = v3 . eq tail(e6) = v5 .
    eq head(e7) = v4 . eq tail(e7) = v6 .
    eq head(e8) = v5 . eq tail(e8) = v6 .
    eq head(e9) = v6 . eq tail(e9) = v2 .
  }
}

module SHORTESTP
{
  protecting (FIXEDPOINT(G <= GRAPH-A, L <= LATTICEtoNAT))
  signature {
    op dist : Edge -> Nat+
  }

  axioms {
    var e : Edge
    var x : Nat+
    eq dist(e1) = 2 .
    eq dist(e2) = 5 .
    eq dist(e3) = 3 .
    eq dist(e4) = 4 .
    eq dist(e5) = 1 .
    eq dist(e6) = 2 .
    eq dist(e7) = 3 .
    eq dist(e8) = 1 .
    eq dist(e9) = 4 .

    eq fe(e) < x > = x + dist(e) .
  }

}

module PAIR (X1 :: TRIV, X2 :: TRIV)
{
  [ Pair ]
  signature {
    op _,_ : Elt.X1 Elt.X2 -> Pair
  }
}

module XSUBV (G :: GRAPHEX, L :: LATTICE-T)
{
  protecting (PAIR(X1 <= view to G { sort Elt -> Vertex },
		   X2 <= view to L { sort Elt -> Elt })
	      * { sort Pair -> XsubV })
}

module XVFUNC (G :: GRAPHEX, L :: LATTICE-T)
{
  protecting (LIST(X <= view to XSUBV(G,L){ sort Elt -> XsubV })
	      * { sort List -> XVfunc })
  signature {
    op _<_> : XVfunc Vertex -> Elt
  }
  axioms {
    var xf : XVfunc
    vars u, v : Vertex
    var e : Elt
    ceq ((u, e) xf) < v > = e if u == v .
    ceq ((u, e) xf) < v > = xf < v > if u =/= v .
  }
}

eof
