module! PAIR [X :: TRIV, Y :: TRIV] {
  signature {
    [ Pair<X;Y> ]

    op <_,_> : Elt.X Elt.Y -> Pair<X;Y>
    op fst_ : Pair<X;Y> -> Elt.X
    op snd_ : Pair<X;Y> -> Elt.Y
  }

  axioms {
    var x : Elt.X
    var y : Elt.Y

    eq fst < x, y > = x .
    eq snd < x, y > = y .
  }
}


module! SET[X :: TRIV] {
  signature {
    [ Elt.X < Set<X> ]

    op empty : -> Set<X> { constr }
    op __ : Set<X> Set<X> -> Set<X> { constr assoc comm id: empty }
    op _in_ : Elt.X Set<X> -> Bool
    op _-_ : Set<X> Set<X> -> Set<X>
  }

  axioms {
    vars e e' : Elt.X
    vars m m' : Set<X>

    eq (e m) (e m') = e m m' .

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


module! LIST[X :: TRIV] {
  import {
    protecting (NAT)
  }

  signature {
    [ Elt.X < List<X> ]

    op nil : -> List<X> { constr }
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


module! DIGRAPH[X :: TRIV]
{
  imports {
    protecting (SET[X])
    protecting (SET[PAIR[X, X] * { sort Pair<X;Y> -> Pair<X;X> }
		    { sort Elt -> Pair<X;X> }]
		* { sort Set<X> -> Set<Pair<X;X>> })
    protecting (LIST[X])
  }

  signature {
    [ DiGraphErr<X> < DiGraph<X>,
      DiGraphOK<X> < DiGraph<X> ]

    op bottom : -> DiGraphErr<X> { constr }
    op empty : -> DiGraphOK<X> { constr }
    op _+_ : DiGraphOK<X> Elt.X -> DiGraphOK<X> { constr }
    op _+_ : DiGraph<X> Elt.X -> DiGraph<X> { constr }
    op _+_->_ : DiGraphOK<X> Elt.X Elt.X -> DiGraph<X> { constr }
    op _+_->_ : DiGraph<X> Elt.X Elt.X -> DiGraph<X> { constr }
    op _+_ : DiGraph<X> DiGraph<X> -> DiGraph<X>
    op vertices : DiGraph<X> -> Set<X>
    op edges : DiGraph<X> -> Set<Pair<X;X>>
    op succ : DiGraph<X> Elt.X -> List<X>
    pred _._->*_ : DiGraph<X> Elt.X Elt.X
    pred reachable : DiGraph<X> Elt.X List<X> Set<X>
    pred cyclefree : DiGraph<X>
    pred cyclefree : DiGraph<X> Set<X>
    op transitivehull : DiGraph<X> -> DiGraph<X>
    op transitivehull : DiGraph<X> Set<X> -> DiGraph<X>
    op transitivehull : DiGraph<X> Elt.X Set<X> -> DiGraph<X>
  }

  axioms {
    vars dg dg' : DiGraph<X>
    vars a a' b : Elt.X
    var s : List<X>
    vars v m : Set<X>

    cq (dg + a) = dg
         if a in vertices(dg) .
    cq (dg + a -> b) = bottom
         if (not (a in vertices(dg))) or (not (b in vertices(dg))) .

    eq dg + bottom = bottom .
    eq dg + empty = dg .
    eq dg + (dg' + a) = (dg + a) + dg' .
    eq dg + (dg' + a -> b) = (dg + a -> b) + dg' .

    eq (dg . a ->* b) = reachable(dg, b, a, empty) .

    eq reachable(dg, b, nil, v) = false .
    eq reachable(dg, b, a s, v) = if (not (a in v))
                                  then (a == b) or reachable(dg, b, s  
							       succ(dg, a), v a)
                                  else reachable(dg, b, s, v)
                                  fi .

    eq vertices(empty) = empty .
    eq vertices(dg + a) = vertices(dg) a .
    eq vertices(dg + a -> b) = vertices(dg) .

    eq edges(empty) = empty .
    eq edges(dg + a) = edges(dg) .
    eq edges(dg + a -> b) = < a, b > edges(dg) .

    eq succ(empty, a) = nil .
    eq succ(dg + a', a) = succ(dg, a) .
    eq succ(dg + a' -> b, a) = if (a == a')
                               then b succ(dg, a)
                               else succ(dg, a)
                               fi .

    eq cyclefree(dg) = cyclefree(dg, vertices(dg)) .
    eq cyclefree(dg, empty) = true .
    eq cyclefree(dg, a m) = (not (dg . a ->* a)) and cyclefree(dg, m) .

    eq transitivehull(bottom) = bottom .
    eq transitivehull(dg) = transitivehull(dg, vertices(dg)) .
    eq transitivehull(dg, a m) = transitivehull(dg, a, vertices(dg)) + 
                                 transitivehull(dg, m) .
    eq transitivehull(dg, a, a' m) = if (dg . a ->* a')
                                     then transitivehull(dg, m) + a -> a'
                                     else transitivehull(dg, m)
                                     fi .
  }
}


module! PARTIALORDER[X :: TRIV] {
  imports {
    protecting (DIGRAPH[X] * { op (_+_->_) -> (_+_<_)
                               op (_._->*_) -> (_._<=_)
                               op vertices -> underlying
                               op cyclefree -> irreflexive })
  }

  signature {
    [ PartialOrderErr<X> < DiGraphErr<X>,
      PartialOrderErr<X> < PartialOrder<X>,
      PartialOrderOK<X> < DiGraphOK<X>,
      PartialOrderOK<X> < PartialOrder<X>,
      PartialOrder<X> < DiGraph<X> ]

    op bottom : -> PartialOrderErr<X> { constr }
    op empty : -> PartialOrderOK<X> { constr }
    op (_+_) : PartialOrderOK<X> Elt.X -> PartialOrderOK<X> { constr }
    op (_+_) : PartialOrder<X> Elt.X -> PartialOrder<X> { constr }
    op (_+_<_) : PartialOrderOK<X> Elt.X Elt.X -> PartialOrder<X>
    op (_+_<_) : PartialOrder<X> Elt.X Elt.X -> PartialOrder<X>
    op underlying : PartialOrder<X> -> Set<X>
    op partialorder : PartialOrder<X> -> Set<Pair<X;X>>
    pred irreflexive : PartialOrder<X>
  }

  axioms {
    var po : PartialOrder<X>
    vars a b : Elt.X

    cq po + a < b = po
         if (po . a <= b) .
    cq po + a < b = bottom
         if (po . b <= a) .

    eq partialorder(po) = edges(transitivehull(po)) .
  }
}


module! ACTION {
  imports {
  }

  signature {
    [ Actions Threads Locations Values ]

    class Action {
      action : Actions
      thread : Threads
      location : Locations
      value : Values
    }

    ops read load use write store assign lock unlock : -> Actions
    ops thd1 thd2 : -> Threads
    ops loc1 loc2 : -> Locations
    ops val1 val2 : -> Values

    pred threadaction : Action
    pred memoryaction : Action
  }

  axioms {
    var x : Action

    eq threadaction(x) = action(x) == load or
                         action(x) == use or
                         action(x) == store or
                         action(x) == assign or
                         action(x) == lock or
                         action(x) == unlock .
    eq memoryaction(x) = action(x) == read or
                         action(x) == store or
                         action(x) == lock or
                         action(x) == unlock .
  }
}


module* RULE-BASE {
  imports {
    protecting (PARTIALORDER[ACTION { sort Elt -> Action }]
		* { sort PartialOrder<X> -> PartialOrder<Action>
		    sort Set<X> -> Set<Action> })
    protecting (SET[TRIV] * { sort Elt -> AllRange
                              sort Set<X> -> Set<AllRange> })
    protecting (SET[TRIV] * { sort Elt -> ExistsRange
                              sort Set<X> -> Set<ExistsRange> })
  }

  signature {
    [ AllRange ExistsRange ]

    op all-range : PartialOrder<Action> -> Set<AllRange>
    op exists-range : PartialOrder<Action> -> Set<ExistsRange>
    pred all-pred : PartialOrder<Action> AllRange
    pred exists-pred : PartialOrder<Action> AllRange ExistsRange
  }
}


module* RULE[X :: RULE-BASE] {
  signature {
    pred rule : PartialOrder<Action>
    pred rule : PartialOrder<Action> Set<AllRange>
    op all : PartialOrder<Action> -> Set<AllRange>
    op all : PartialOrder<Action> Set<AllRange> -> Set<AllRange>
    pred exists : PartialOrder<Action> AllRange
    pred exists : PartialOrder<Action> AllRange Set<ExistsRange>
  }

  axioms {
    var po : PartialOrder<Action>
    var x : AllRange
    var m : Set<AllRange>
    var y : ExistsRange
    var n : Set<ExistsRange>

    eq rule(po) = rule(po, all(po)) .
    eq rule(po, empty) = true .
    eq rule(po, x m) = exists(po, x) or rule(po, m) .

    eq all(po) = all(po, all-range(po)) .
    eq all(po, empty) = empty .
    eq all(po, x m) = if all-pred(po, x)
                      then x all(po, m)
                      else all(po, m)
                      fi .

    eq exists(po, x) = exists(po, x, exists-range(po)) .
    eq exists(po, x, empty) = false .
    eq exists(po, x, y n) = exists-pred(po, x, y) or exists(po, x, n) .
  }
}


module RULES {
  imports {
    protecting (NAT)
    protecting (PAIR[ACTION{ sort Elt -> Action },
		     ACTION{ sort Elt -> Action }] 
		* { sort Pair<X;Y> -> Pair<Action;Action> })
    protecting (PARTIALORDER[ACTION{ sort Elt -> Action }] 
		* { sort PartialOrder<X> -> PartialOrder<Action>
		    sort Set<X> -> Set<Action>
		    sort Set<Pair<X;X>> -> Set<Pair<Action;Action>> })
  }

  signature {
    pred assign<load : PartialOrder<Action> Pair<Action;Action>
    pred <store< : PartialOrder<Action> Pair<Action;Action> Action
  }

  axioms {
    var po : PartialOrder<Action>
    vars x x' x'' r l u w s s' a o o' n : Action

    -- Rule 3
    eq assign<load(po, < a, l >) = action(a) == assign and
                                   action(l) == load and
                                   thread(a) == thread(l) and
                                   location(a) == location(l) .
    eq <store<(po, < x, x' >, s) = action(s) == store and
                                   thread(s) == thread(x) and
                                   location(s) == location(x) and
                                   (po . x <= s) and (po . s <= x') .
  }
}


make RULE3 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Pair<Action;Action>>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op exists-range -> underlying,
                         op all-range -> partialorder,
                         op all-pred -> assign<load,
                         op exists-pred -> <store< }])

module! EVENTSPACE {
  imports {
    protecting (ACTION)
    protecting (SET[ACTION { sort Elt -> Action }] * { sort Set<X> -> Set<Action> })
    protecting (PARTIALORDER[ACTION { sort Elt -> Action }])
  }

  signature {
    [ EventSpace < PartialOrder ]

    op continuations : EventSpace -> Set<Action>
  }
}

eof
