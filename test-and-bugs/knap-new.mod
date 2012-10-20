-- Return-Path: knapp@informatik.uni-muenchen.de 
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id EAA01842 for <sawada@sras75.sra.co.jp>; Wed, 1 Apr 1998 04:45:11 +0900
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id EAA25569
-- 	for <sawada@sras75.sra.co.jp>; Wed, 1 Apr 1998 04:45:17 +0900 (JST)
-- Received: from jive.pst.informatik.uni-muenchen.de (jive.pst.informatik.uni-muenchen.de [129.187.228.173])
-- 	by sraigw.sra.co.jp (8.8.7/3.6Wbeta7-sraigw) with ESMTP id EAA06970
-- 	for <sawada@sras75.sra.co.jp>; Wed, 1 Apr 1998 04:44:58 +0859 (JST)
-- Received: from informatik.uni-muenchen.de (knapp@localhost [127.0.0.1])
-- 	by jive.pst.informatik.uni-muenchen.de (8.8.5/8.8.5) with ESMTP id VAA11066
-- 	for <sawada@sras75.sra.co.jp>; Tue, 31 Mar 1998 21:44:52 +0200
-- Sender: knapp@jive.pst.informatik.uni-muenchen.de
-- Message-ID: <352147B3.A3A11DB8@informatik.uni-muenchen.de>
-- Date: Tue, 31 Mar 1998 21:44:51 +0200
-- From: Alexander Knapp <knapp@informatik.uni-muenchen.de>
-- Organization: Ludwig-Maximilians-Universit舩 Mchen
-- X-Mailer: Mozilla 4.04j2 [en] (X11; I; Linux 2.0.30 i686)
-- MIME-Version: 1.0
-- To: Toshimi & <sawada@sras75.sra.co.jp>
-- Subject: Re: CafeOBJ1.4b5
-- References: <3506748E.A4CDE3CF@informatik.uni-muenchen.de> <199803120441.NAA23736@sras75.sra.co.jp>
-- Content-Type: multipart/mixed; boundary="------------509F773938A9E9CAB6DFA7AC"
-- Content-Length: 13899

-- This is a multi-part message in MIME format.
-- --------------509F773938A9E9CAB6DFA7AC
-- Content-Type: text/plain; charset=us-ascii
-- Content-Transfer-Encoding: 7bit

-- Dear Toshimi!

-- 	First of all, an impolite question: Have you sent me a mail during the
-- last view days?  If so, could you please resend it?, I had some troubles
-- with receiving mail.  Thanks!
-- 	Meanwhile I encountered another problem with CafeOBJ version 1.4 that
-- did not occur in version 1.3.1 (Roman patch): After reading in
-- structures.mod (find it attached), CafeOBJ 1.3.1 produces:

-- CafeOBJ> select PARTIALORDER

-- PARTIALORDER(X)> red underlying((null):PartialOrderOK<X>) .
-- -- reduce in PARTIALORDER(X) : underlying(null)
-- empty : Set<X>
-- (0.020 sec for parse, 2 rewrites(0.000 sec), 2 match attempts)

-- which seems correct, but CafeOBJ 1.4 produces:

-- CafeOBJ> select PARTIALORDER

-- PARTIALORDER(X)> red underlying((null):PartialOrderOK<X>) .
-- -- reduce in PARTIALORDER(X) : underlying(null)
-- vertices(null) : Set<X>
-- (0.000 sec for parse, 1 rewrites(0.000 sec), 5 match attempts)

-- 	I'd preferred CafeOBJ 1.3.1's solution...

-- Best,
-- Alexander.

-- -- 

-- Alexander Knapp
-- URL: http://www.pst.informatik.uni-muenchen.de/~knapp/
-- --------------509F773938A9E9CAB6DFA7AC
-- Content-Type: text/plain; charset=us-ascii; name="structures.mod"
-- Content-Disposition: inline; filename="structures.mod"
-- Content-Transfer-Encoding: 7bit

module* TRIVBOTTOM {
  signature {
    [ Elt ]

    op bottom : -> Elt
  }
}


module! PAIR(X :: TRIV, Y :: TRIV) {
  signature {
    [ Pair<X;Y> ]

    op <<_,_>> : Elt.X Elt.Y -> Pair<X;Y>
    op fst_ : Pair<X;Y> -> Elt.X
    op snd_ : Pair<X;Y> -> Elt.Y
  }

  axioms {
    var x : Elt.X
    var y : Elt.Y

    eq fst << x, y >> = x .
    eq snd << x, y >> = y .
  }
}


module! TRIPLE(X :: TRIV, Y :: TRIV, Z :: TRIV) {
  signature {
    [ Triple<X;Y;Z> ]

    op <<_,_,_>> : Elt.X Elt.Y Elt.Z -> Triple<X;Y;Z>
    op fst_ : Triple<X;Y;Z> -> Elt.X
    op snd_ : Triple<X;Y;Z> -> Elt.Y
    op thd_ : Triple<X;Y;Z> -> Elt.Z
  }

  axioms {
    var x : Elt.X
    var y : Elt.Y
    var z : Elt.Z

    eq fst << x, y, z >> = x .
    eq snd << x, y, z >> = y .
    eq thd << x, y, z >> = z .
  }
}


module! QUADRUPLE(W :: TRIV, X :: TRIV, Y :: TRIV, Z :: TRIV) {
  signature {
    [ Quadruple<W;X;Y;Z> ]

    op <<_,_,_,_>> : Elt.W Elt.X Elt.Y Elt.Z -> Quadruple<W;X;Y;Z>
    op fst_ : Quadruple<W;X;Y;Z> -> Elt.W
    op snd_ : Quadruple<W;X;Y;Z> -> Elt.X
    op thd_ : Quadruple<W;X;Y;Z> -> Elt.Y
    op fth_ : Quadruple<W;X;Y;Z> -> Elt.Z
  }

  axioms {
    var w : Elt.W
    var x : Elt.X
    var y : Elt.Y
    var z : Elt.Z

    eq fst << w, x, y, z >> = w .
    eq snd << w, x, y, z >> = x .
    eq thd << w, x, y, z >> = y .
    eq fth << w, x, y, z >> = z .
  }
}


module! SET(X :: TRIV) {
  signature {
    [ Elt.X < Set<X> ]

    op empty : -> Set<X> { constr }
    op __ : Set<X> Set<X> -> Set<X> { constr assoc comm idem id: empty }
    op _in_ : Elt.X Set<X> -> Bool
    op _-_ : Set<X> Set<X> -> Set<X>
  }

  axioms {
    vars e e' : Elt.X
    vars m m' : Set<X>

    eq e in empty = false .
    eq e in (e' m) = if (e == e')
                     then true
                     else e in m
                     fi .

    cq (e m) - m' = m - m'
       if (e in m') .
    cq (e m) - m' = e (m - m')
       if (not (e in m')) .
    eq empty - m' = empty .
  }
}


module! LIST(X :: TRIV) {
  import {
    protecting (NAT)
  }

  signature {
    [ Elt.X < List+<X> < List<X> ]

    op nil : -> List<X> { constr }
    op __ : List<X> List+<X> -> List+<X> { constr }
    op __ : List+<X> List<X> -> List+<X> { constr }
    op __ : List<X> List<X> -> List<X> { constr assoc id: nil }
    op |_| : List<X> -> Nat
    op _in_ : Elt.X List<X> -> Bool
  }

  axioms {
    vars e e' : Elt.X
    var l  : List<X>

    eq e in nil = false .
    eq e in e' = (e == e') .
    eq e in (e' l) = (e == e') or (e in l) .

    eq | nil | = 0 .
    eq | e l | = 1 + | l | .
  }
}


module! STACK(X :: TRIV) {
  signature {
    [ StackErr<X> Stack+<X> < StackOK<X> < Stack<X> ]

    op bottom : -> StackErr<X> { constr }
    op empty : -> StackOK<X> { constr }
    op push : Elt.X StackOK<X> -> Stack+<X> { constr }
    op push : Elt.X Stack<X> -> Stack<X> { constr }

    op pop : Stack+<X> -> StackOK<X>
    op pop : Stack<X> -> Stack<X>
    op top : Stack+<X> -> Elt.X
    op top : Stack<X> -> Elt.X
  }

  axioms {
    var s : Stack<X>
    var s' : StackOK<X>
    var x : Elt.X

    eq pop(bottom) = bottom .
    eq pop(empty) = bottom .
    eq pop(push(x, s)) = s .

    eq top(push(x, s')) = x .
  }
}


module! PARTIALFUNCTION(X :: TRIV, Y :: TRIVBOTTOM) {
  imports {
    protecting (SET(X))
    protecting (SET(Y) * { sort Set<X> -> Set<Y> })
  }

  signature {
    [ PartialFunction<X;Y> ]

    op undefined : -> PartialFunction<X;Y> { constr }
    op _[_|->_] : PartialFunction<X;Y> Elt.X Elt.Y -> PartialFunction<X;Y> { constr }
    op __ : PartialFunction<X;Y> Elt.X -> Elt.Y
    op source : PartialFunction<X;Y> -> Set<X>
    op range : PartialFunction<X;Y> -> Set<Y>
  }

  axioms {
    var f : PartialFunction<X;Y>
    vars x x' : Elt.X
    var y : Elt.Y

    cq f [ x |-> y ] = f
         if y == bottom .

    eq undefined x = bottom .
    eq (f [ x' |-> y ]) x = if (x == x')
                            then y
                            else f x
                            fi .

    eq source(undefined) = (empty):Set<X> .
    eq source(f [ x |-> y ]) = x source(f) .

    eq range(undefined) = (empty):Set<Y> .
    eq range(f [ x |-> y ]) = y range(f) .
  }
}


module! DIGRAPH(X :: TRIV) {
  imports {
    protecting (SET(X))
    protecting (SET(PAIR(X, X) * { sort Pair<X;Y> -> Pair<X;X>, op (<<_,_>>) -> (<<_,_>>) } { sort Elt -> Pair<X;X> }) * { sort Set<X> -> Set<Pair<X;X>> })
    protecting (LIST(X))
  }

  signature {
    [ DiGraphErr<X> DiGraphOK<X> < DiGraph<X>,
      Elt.X Pair<X;X> < DiGraphOK<X> ]

    op bottom : -> DiGraphErr<X> { constr }
    op null : -> DiGraphOK<X> { constr }
    op _+_ : DiGraph<X> DiGraph<X> -> DiGraph<X> { constr assoc comm prec: 40 }
    op _+_ : DiGraphOK<X> DiGraphOK<X> -> DiGraphOK<X> { constr assoc comm prec: 40 }
    op _+_->_ : DiGraph<X> Elt.X Elt.X -> DiGraph<X> { l-assoc prec: 41 }
    op make-digraph : Set<Pair<X;X>> -> DiGraph<X>
    op vertices : DiGraph<X> -> Set<X>
    op edges : DiGraph<X> -> Set<Pair<X;X>>
    op succ : DiGraph<X> Elt.X -> List<X>
    pred _._->*_ : DiGraph<X> Elt.X Elt.X
    pred _._->+_ : DiGraph<X> Elt.X Elt.X
    pred reachable : DiGraph<X> Elt.X List<X> Set<X>
    pred cyclefree : DiGraph<X>
    pred cyclefree : DiGraph<X> Set<X>
    op transitivehull : DiGraph<X> -> DiGraph<X>
    op transitivehull : DiGraph<X> Set<X> -> DiGraph<X>
    op transitivehull : DiGraph<X> Elt.X Set<X> -> DiGraph<X>
    op union : DiGraph<X> DiGraph<X> -> DiGraph<X>
  }

  axioms {
    vars dg dg' dg'' : DiGraph<X>
    vars a a' b b' : Elt.X
    var p : Pair<X;X>
    var s : List<X>
    vars v m : Set<X>
    var mp : Set<Pair<X;X>>

    eq dg + bottom = bottom .
    eq dg + null = dg .
    -- eq a + a = a .
    -- eq p + p = p .
    -- cq a + << a', b' >> = << a', b' >>
    --      if (a == a') or (a == b') .

    eq (dg + a -> b) = dg + << a, b >> .

    eq (dg . a ->* b) = reachable(dg, b, a, empty) .
    eq (dg . a ->+ b) = reachable(dg, b, succ(dg, a), empty) .

    eq make-digraph(empty) = null .
    eq make-digraph(<< a, b >> mp) = (null + a -> b) + make-digraph(mp) .

    eq reachable(dg, b, nil, v) = false .
    eq reachable(dg, b, a s, v) = if (not (a in v))
                                  then (a == b) or reachable(dg, b, s succ(dg, a), v a)
                                  else reachable(dg, b, s, v)
                                  fi .

    eq vertices(null) = empty .
    eq vertices(a) = a .
    eq vertices(<< a, b >>) = vertices(a) vertices(b) .
    eq vertices(dg + dg') = vertices(dg) vertices(dg') .

    eq edges(null) = empty .
    eq edges(a) = empty .
    eq edges(p) = p .
    eq edges(dg + dg') = edges(dg) edges(dg') .

    eq succ(null, a) = nil .
    eq succ(a', a) = nil .
    eq succ(<< a', b' >>, a) = if (a == a')
                               then b'
                               else nil
                               fi .
    eq succ(dg + dg', a) = succ(dg, a) succ(dg', a) .

    eq cyclefree(dg) = cyclefree(dg, vertices(dg)) .
    eq cyclefree(dg, empty) = true .
    eq cyclefree(dg, a m) = (not (dg . a ->+ a)) and cyclefree(dg, m) .

    eq transitivehull(bottom) = bottom .
    eq transitivehull(dg) = transitivehull(dg, vertices(dg)) .
    eq transitivehull(dg, empty) = dg .
    eq transitivehull(dg, a m) = transitivehull(dg, a, vertices(dg)) + transitivehull(dg, m) .
    eq transitivehull(dg, a, empty) = dg .
    eq transitivehull(dg, a, a' m) = if (dg . a ->* a')
                                     then transitivehull(dg, a, m) + a -> a'
                                     else transitivehull(dg, a, m)
                                     fi .
  }
}


module! PARTIALORDER(X :: TRIV) {
  imports {
    protecting (DIGRAPH(X) * { op (_+_->_) -> (_+_<_)
                               op (_._->*_) -> (_._<=_) })
  }

  signature {
    [ PartialOrderErr<X> < DiGraphErr<X> PartialOrder<X> < DiGraph<X>,
      Elt.X Pair<X;X> < PartialOrderOK<X> < DiGraphOK<X> PartialOrder<X> < DiGraph<X> ]

    op bottom : -> PartialOrderErr<X> { constr }
    op null : -> PartialOrderOK<X> { constr }
    op (_+_) : PartialOrderOK<X> PartialOrderOK<X> -> PartialOrderOK<X> { constr assoc comm prec: 40 }
    op (_+_) : PartialOrder<X> PartialOrder<X> -> PartialOrder<X> { constr assoc comm prec: 40 }
    op (_+_<_) : PartialOrder<X> Elt.X Elt.X -> PartialOrder<X> { l-assoc prec: 41 }
    op singleton : PartialOrder<X> -> Set<X>
    op underlying : PartialOrder<X> -> Set<X>
    op relation : PartialOrder<X> -> Set<Pair<X;X>>
    op fullrelation : PartialOrder<X> -> Set<Pair<X;X>>
    op fullrelation : PartialOrder<X> Set<X> -> Set<Pair<X;X>>
    op fullrelation : PartialOrder<X> Set<X> Set<X> -> Set<Pair<X;X>>
    op partialorder : DiGraph<X> -> PartialOrder<X>
    op make-partialorder : Set<Pair<X;X>> -> PartialOrder<X>
    op dg2po : DiGraph<X> -> PartialOrder<X>
    op minimals : PartialOrder<X> Set<X> -> Set<X>
    op minimals : PartialOrder<X> Set<X> Set<X> -> Set<X>
    pred minimal : PartialOrder<X> Set<X> Elt.X
  }

  axioms {
    vars dg dg' : DiGraph<X>
    vars po po' : PartialOrder<X>
    vars m ma mb : Set<X>
    var mp : Set<Pair<X;X>>
    vars a b : Elt.X
    var p : Pair<X;X>

    eq po + bottom = bottom .
    eq po + null = po .
    eq po + a < b = po + << a, b >> .
    -- cq po + << a, b >> = po
    --      if (po . a <= b) .
    -- cq po + << a, b >> = bottom
    --      if (po . b <= a) .

    eq singleton(bottom) = empty .
    eq singleton(null) = empty .
    eq singleton(a) = a .
    eq singleton(p) = singleton(fst p) .
    eq singleton(po + po') = if (singleton(po) == (empty):Set<X>)
                             then singleton(po')
                             else singleton(po)
                             fi .

    eq underlying(po) = vertices(po) .

    eq relation(po) = edges(transitivehull(po)) .

    eq fullrelation(po) = fullrelation(po, underlying(po)) .
    eq fullrelation(po, empty) = empty .
    eq fullrelation(po, a m) = fullrelation(po, a, underlying(po)) .
    eq fullrelation(po, a, empty) = empty .
    eq fullrelation(po, a, b m) = << a, b >> fullrelation(po, a, m) .

    eq partialorder(dg) = if (cyclefree(dg))
                          then dg2po(dg)
                          else (bottom):PartialOrderErr<X>
                          fi .

    eq dg2po((null):DiGraphOK<X>) = null .
    eq dg2po(a) = a .
    eq dg2po(<< a, b >>) = (null):PartialOrderOK<X> + a < b .
    eq dg2po(dg + dg') = dg2po(dg) + dg2po(dg') .

    eq make-partialorder(mp) = partialorder(make-digraph(mp)) .

    eq minimals(po, m) = minimals(po, m, m) .
    eq minimals(po, m, empty) = empty .
    eq minimals(po, m, a ma) = if minimal(po, m, a)
                               then a minimals(po, m, ma)
                               else minimals(po, m, ma)
                               fi . 
    eq minimal(po, empty, a) = true .
    eq minimal(po, b mb, a) = if ((po . b <= a) and (a =/= b))
                              then false
                              else minimal(po, mb, a)
                              fi .
  }
}


-- provide structures

-- eof


module! TEST {
  imports {
    protecting (PARTIALORDER(STRING { sort Elt -> String }) *
                  { sort Set<X> -> Set<String>,
                    sort DiGraph<X> -> DiGraph<String>,
                    sort PartialOrder<X> -> PartialOrder<String> })
  }

  signature {
    op rulenames : -> Set<String>
    op priorities : -> PartialOrder<String>
  }

  axioms {
    eq rulenames = underlying(priorities) .

    eq priorities = make-partialorder(<< "assign2", "assign1" >>
                                      << "assign3'", "assign2" >>
                                      << "assign4'", "assign2" >>
                                      << "unop2!", "unop1" >>
                                      << "access2", "access1" >>
                                      << "pth2", "pth1" >>
                                      << "decl2", "decl1" >>
                                      << "declseq2", "declseq1" >>
                                      << "locvardecl2", "locvardecl1" >>
                                      << "locvardeclstat2", "locvardeclstat1" >>
                                      << "statseq2", "statseq1" >>
                                      << "expstat2", "expstat1" >>
                                      << "block1", "block2" >>) +
                                      "new" + "val'" + "var'" + "skip" .
  }
}


-- provide structures

-- eof


select TEST

red priorities .

-- --------------509F773938A9E9CAB6DFA7AC--


