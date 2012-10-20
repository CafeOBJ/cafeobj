module! PAIR[X :: TRIV, Y :: TRIV] {
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


module! DIGRAPH[X :: TRIV] {
  imports {
    protecting (SET[X])
    protecting (SET[PAIR[X, X] * { sort Pair<X;Y> -> Pair<X;X> } { sort Elt  
-> Pair<X;X> }] * { sort Set<X> -> Set<Pair<X;X>> })
    protecting (LIST[X])
  }

  signature {
    [ DiGraphErr<X> < DiGraph<X>,
      DiGraphOK<X> < DiGraph<X> ]

    op bottom : -> DiGraphErr<X> { constr }
    op null : -> DiGraphOK<X> { constr }
    op _+_ : DiGraphOK<X> Elt.X -> DiGraphOK<X> { constr }
    op _+_ : DiGraph<X> Elt.X -> DiGraph<X> { constr }
    op _+_->_ : DiGraphOK<X> Elt.X Elt.X -> DiGraph<X> { constr }
    op _+_->_ : DiGraph<X> Elt.X Elt.X -> DiGraph<X> { constr }
    op _+_ : DiGraph<X> DiGraph<X> -> DiGraph<X>
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
    eq dg + null = dg .
    eq dg + (dg' + a) = (dg + a) + dg' .
    eq dg + (dg' + a -> b) = (dg + a -> b) + dg' .

    eq (dg . a ->* b) = reachable(dg, b, a, empty) .
    eq (dg . a ->+ b) = reachable(dg, b, succ(dg, a), empty) .

    eq reachable(dg, b, nil, v) = false .
    eq reachable(dg, b, a s, v) = if (not (a in v))
                                  then (a == b) or reachable(dg, b,
							     s succ(dg, a), v a)
                                  else reachable(dg, b, s, v)
                                  fi .

    eq vertices(null) = empty .
    eq vertices(dg + a) = vertices(dg) a .
    eq vertices(dg + a -> b) = vertices(dg) .

    eq edges(null) = empty .
    eq edges(dg + a) = edges(dg) .
    eq edges(dg + a -> b) = < a, b > edges(dg) .

    eq succ(null, a) = nil .
    eq succ(dg + a', a) = succ(dg, a) .
    eq succ(dg + a' -> b, a) = if (a == a')
                               then b succ(dg, a)
                               else succ(dg, a)
                               fi .

    eq cyclefree(dg) = cyclefree(dg, vertices(dg)) .
    eq cyclefree(dg, empty) = true .
    eq cyclefree(dg, a m) = (not (dg . a ->+ a)) and cyclefree(dg, m) .

    eq transitivehull(bottom) = bottom .
    eq transitivehull(dg) = transitivehull(dg, vertices(dg)) .
    eq transitivehull(dg, empty) = dg .
    eq transitivehull(dg, a m) = transitivehull(dg, a, vertices(dg)) +  
transitivehull(dg, m) .
    eq transitivehull(dg, a, empty) = dg .
    eq transitivehull(dg, a, a' m) = if (dg . a ->* a')
                                     then transitivehull(dg, a, m) + a -> a'
                                     else transitivehull(dg, a, m)
                                     fi .
  }
}


module! PARTIALORDER[X :: TRIV] {
  imports {
    protecting (DIGRAPH[X] * { op (_+_->_) -> (_+_<_)
                               op (_._->*_) -> (_._<=_)
                               op vertices -> underlying })
  }

  signature {
    [ PartialOrderErr<X> < DiGraphErr<X>,
      PartialOrderErr<X> < PartialOrder<X>,
      PartialOrderOK<X> < DiGraphOK<X>,
      PartialOrderOK<X> < PartialOrder<X>,
      PartialOrder<X> < DiGraph<X> ]

    op bottom : -> PartialOrderErr<X> { constr }
    op null : -> PartialOrderOK<X> { constr }
    op (_+_) : PartialOrderOK<X> Elt.X -> PartialOrderOK<X> { constr }
    op (_+_) : PartialOrder<X> Elt.X -> PartialOrder<X> { constr }
    op (_+_<_) : PartialOrderOK<X> Elt.X Elt.X -> PartialOrder<X> { constr }
    op (_+_<_) : PartialOrder<X> Elt.X Elt.X -> PartialOrder<X> { constr }
    pred (_._<=_) : PartialOrder<X> Elt.X Elt.X
    op singleton : PartialOrder<X> -> Set<X>
    op underlying : PartialOrder<X> -> Set<X>
    op relation : PartialOrder<X> -> Set<Pair<X;X>>
    op fullrelation : PartialOrder<X> -> Set<Pair<X;X>>
    op fullrelation : PartialOrder<X> Set<X> -> Set<Pair<X;X>>
    op fullrelation : PartialOrder<X> Set<X> Set<X> -> Set<Pair<X;X>>
    op partialorder : DiGraph<X> -> PartialOrder<X>
    op dg2po : DiGraph<X> -> PartialOrder<X>
  }

  axioms {
    var dg : DiGraph<X>
    var po : PartialOrder<X>
    var m : Set<X>
    vars a b : Elt.X

    cq po + a < b = po
         if (po . a <= b) .
    cq po + a < b = bottom
         if (po . b <= a) .

    eq singleton(null) = empty .
    eq singleton(po + a) = a .
    eq singleton(po + a < b) = singleton(po) .

    eq relation(po) = edges(transitivehull(po)) .

    eq fullrelation(po) = fullrelation(po, underlying(po)) .
    eq fullrelation(po, empty) = empty .
    eq fullrelation(po, a m) = fullrelation(po, a, underlying(po)) .
    eq fullrelation(po, a, empty) = empty .
    eq fullrelation(po, a, b m) = < a, b > fullrelation(po, a, m) .

    eq partialorder(dg) = if (cyclefree(dg))
                          then dg2po(dg)
                          else (bottom):PartialOrderErr<X>
                          fi .

    eq dg2po((null):DiGraphOK<X>) = null .
    eq dg2po(dg + a) = dg2po(dg) + a .
    eq dg2po(dg + a < b) = dg2po(dg) + a < b .
  }
}


module! ACTION {
  imports {
  }

  signature {
    [ Actions Threads Objects Locations Values,
      Locations Objects < LocObjs ]

    class Action {
      action : Actions
      thread : Threads
    }

    class ASR-Action [ Action ] {
      location : Locations
      value : Values
    }

    class ULW-Action [ Action ] {
      location : Locations
    }

    class LU-Action [ Action ] {
      object : Objects
    }

    ops read load use write store assign lock unlock : -> Actions
    ops thd1 thd2 : -> Threads
    ops obj1 obj2 : -> Objects
    ops loc1 loc2 : -> Locations
    ops val1 val2 : -> Values

    pred threadaction : Action
    pred memoryaction : Action
    op locobj : Action -> LocObjs
  }

  axioms {
    var x : Action
    var ulw : ObjectId
    var l : Locations

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

    eq locobj(x) = if (action(x) == lock or action(x) == unlock)
                   then object(x)
                   else location(x)
                   fi .
  }
}


module* RULE-BASE {
  imports {
    protecting (PARTIALORDER[ACTION { sort Elt -> Action }] * { sort  
PartialOrderOK<X> -> PartialOrderOK<Action>
                                                                sort  
PartialOrder<X> -> PartialOrder<Action>
                                                                sort Set<X>  
-> Set<Action>
                                                                sort  
Pair<X;X> -> Pair<Action;Action>
                                                                sort  
Set<Pair<X;X>> -> Set<Pair<Action;Action>> })
    protecting (SET[TRIV] * { sort Elt -> AllRange
                              sort Set<X> -> Set<AllRange> })
    protecting (SET[TRIV] * { sort Elt -> ExistsRange
                              sort Set<X> -> Set<ExistsRange> })
  }

  signature {
    [ AllRange ExistsRange ]

    op all-range : PartialOrder<Action> -> Set<AllRange>
    op exists-range : PartialOrder<Action> -> Set<ExistsRange>
    pred all-pred : AllRange
    pred ext-pred : AllRange Action
    pred exists-pred : PartialOrder<Action> AllRange ExistsRange
  }
}


module* RULE[X :: RULE-BASE] {
  signature {
    pred rule : PartialOrder<Action>
    pred rule-ext : PartialOrder<Action> Action
    pred rule : PartialOrder<Action> Set<AllRange>
    op filter : Set<AllRange> -> Set<AllRange>
    op filter-ext : Set<AllRange> Action -> Set<AllRange>
    pred exists : PartialOrder<Action> AllRange Set<ExistsRange>
  }

  axioms {
    var po : PartialOrder<Action>
    var a : Action
    var x : AllRange
    var m : Set<AllRange>
    var y : ExistsRange
    var n : Set<ExistsRange>

    eq rule(po) = rule(po, filter(all-range(po))) .
    eq rule-ext(po, a) = rule(po, filter-ext(all-range(po), a)) .

    eq rule(po, empty) = true .
    eq rule(po, x m) = exists(po, x, exists-range(po)) and rule(po, m) .

    eq filter(empty) = empty .
    eq filter(x m) = if all-pred(x)
                     then x filter(m)
                     else filter(m)
                     fi .

    eq filter-ext(empty, a) = empty .
    eq filter-ext(x m, a) = if all-pred(x) and ext-pred(x, a)
                            then x filter-ext(m, a)
                            else filter-ext(m, a)
                            fi .

    eq exists(po, x, empty) = false .
    eq exists(po, x, y n) = exists-pred(po, x, y) or exists(po, x, n) .
  }
}


module RULES {
  imports {
    protecting (NAT)
    protecting (PARTIALORDER[ACTION { sort Elt -> Action }] * { sort  
PartialOrderOK<X> -> PartialOrderOK<Action>
                                                                sort  
PartialOrder<X> -> PartialOrder<Action>
                                                                sort Set<X>  
-> Set<Action>
                                                                sort  
Pair<X;X> -> Pair<Action;Action>
                                                                sort  
Set<Pair<X;X>> -> Set<Pair<Action;Action>> })
  }

  signature {
    op # : PartialOrder<Action> Action -> Nat
    pred ext-in : Action Action
    pred ext-adjoin : Pair<Action;Action> Action

    pred samethread : Pair<Action;Action>
    pred samelocobj : Pair<Action;Action>
    pred ordered : PartialOrder<Action> Pair<Action;Action> Action
    pred assign<load : Pair<Action;Action>
    pred <store< : PartialOrder<Action> Pair<Action;Action> Action
    pred store<store : Pair<Action;Action>
    pred <assign< : PartialOrder<Action> Pair<Action;Action> Action
    pred use : Action
    pred load< : PartialOrder<Action> Action Action
    pred assign<-or-load< : PartialOrder<Action> Action Action
    pred store : Action
    pred assign< : PartialOrder<Action> Action Action
    pred assign<store : Pair<Action;Action>
    pred <assign/v< : PartialOrder<Action> Pair<Action;Action> Action
    pred load : Action
    pred read-n< : PartialOrder<Action> Action Action
    pred write : Action
    pred store-n< : PartialOrder<Action> Action Action
    pred store-m<load-n : Pair<Action;Action>
    pred write-m<read-n : PartialOrder<Action> Pair<Action;Action>
      Pair<Action;Action>
    pred unlock : Action
    pred lock-n< : PartialOrder<Action> Action Action
    pred lock-n<lock : Pair<Action;Action>
    pred unlock-n< : PartialOrder<Action> Pair<Action;Action> Action
    pred assign<unlock : Pair<Action;Action>
    pred <store-n<write-n< : PartialOrder<Action> Pair<Action;Action>  
      Pair<Action;Action>
    pred lock<use : Pair<Action;Action>
    pred <assign\l<-or-<read-n<load-n< : PartialOrder<Action>
      Pair<Action;Action> Pair<Action;Action>
    pred lock<store : Pair<Action;Action>
    pred <assign\l< : PartialOrder<Action> Pair<Action;Action> Action
  }

  axioms {
    var po : PartialOrder<Action>
    vars x x' x'' r l u w s s' a o o' n a/l o/r : Action

    eq #((null):PartialOrderOK<Action>, x) = 0 .
    eq #(po + x', x) = if (action(x') == action(x) and
                           thread(x') == thread(x) and
                           locobj(x') == locobj(x) and
                           (po . x' <= x))
                       then #(po, x) + 1
                       else #(po, x)
                       fi .
    eq #(po + x' < x'', x) = #(po, x) .

    eq ext-in(x', x) = x == x' .
    eq ext-adjoin(< x', x'' >, x) = x == x'' .

    -- Rule 1
    eq samethread(< x, x' >) = threadaction(x) and threadaction(x') and
                               thread(x) == thread(x') .

    eq ordered(po, < x, x' >, x'') = (po . x <= x') or (po . x' <= x) .

    -- Rule 2
    -- eq samelocobj(< x, x' >, x'') = memoryaction(x) and memoryaction(x') and
    --                                locobj(x) == locobj(x') .
    eq samelocobj(< x, x' >) = memoryaction(x) and memoryaction(x') and
                               locobj(x) == locobj(x') .

    -- Rule 3
    eq assign<load(< a, l >) = action(a) == assign and
                               action(l) == load and
                               thread(a) == thread(l) and
                               location(a) == location(l) .
    eq <store<(po, < x, x' >, s) = action(s) == store and
                                   thread(s) == thread(x) and
                                   location(s) == location(x) and
                                   (po . x <= s) and (po . s <= x') .

    -- Rule 4
    eq store<store(< s, s' >) = action(s) == store and action(s') == store and
                                thread(s) == thread(s') and
                                location(s) == location(s') .
    eq <assign<(po, < x, x' >, a) = action(a) == assign and
                                    thread(a) == thread(x) and
                                    location(a) == location(x) and
                                    (po . x <= a) and (po . a <= x') .

    -- Rule 5
    eq use(u) = action(u) == use .
    eq assign<-or-load<(po, x, x') = (action(x') == assign or action(x') == load) and
                                     thread(x') == thread(x) and
                                     location(x') == location(x) and
                                     (po . x <= x') .

    -- Rule 6
    eq store(s) = action(s) == store .
    eq assign<(po, x, a) = action(a) == assign and
                           thread(a) == thread(x) and
                           location(a) == location(x) and
                           (po . a <= x) .

    -- Rule 7
    eq assign<store(< a, l >) = action(a) == assign and action(l) == store and
                                thread(a) == thread(l) and
                                location(a) == location(l) .

    eq <assign/v<(po, < x, x' >, a) = (value(x) == value(x')) or
                                      (action(a) == assign and
                                       thread(a) == thread(x) and
                                       location(a) == location(x) and
                                       (a =/= x) and
                                       (po . x <= a) and (po . a <= x')) .

    -- Rule 8
    eq load(l) = action(l) == load .
    eq read-n<(po, x, r) = action(r) == read and
                           thread(r) == thread(x) and
                           location(r) == location(x) and
                           (#(po, x) == #(po, r)) and
                           (po . r <= x) .

    -- Rule 9
    eq write(w) = action(w) == write .
    eq store-n<(po, x, s) = action(s) == store and
                            thread(s) == thread(x) and
                            location(s) == location(x) and
                            #(po, x) == #(po, s) and
                            (po . s <= x) .

    -- Rule 10
    eq store-m<load-n(< s, l >) = action(s) == store and
                                  action(l) == load and
                                  thread(s) == thread(l) and
                                  location(s) == location(l) .
    eq write-m<read-n(po, < x, x' >, < w, r >) = action(w) == write and
                                                 action(r) == read and
                                                 thread(w) == thread(r) and
                                                 thread(w) == thread(x) and
                                                 location(w) == location(r) and
                                                 location(w) == location(x) and
                                                 #(po, w) == #(po, x) and
                                                 #(po, r) == #(po, x') .

    -- Rule 11
    eq unlock(n) = action(n) == unlock .
    eq lock-n<(po, x, o) = action(o) == lock and
                           thread(o) == thread(x) and
                           object(o) == object(x) and
                           #(po, o) == #(po, x) and
                           (po . o <= x) .

    -- Rule 12
    eq lock-n<lock(< o, o' >) = action(o) == lock and
                                action(o') == lock and
                                thread(o) =/= thread(o') and
                                object(o) == object(o') .
    eq unlock-n<(po, < x, x' >, n) = action(n) == unlock and
                                   thread(n) == thread(x) and
                                   object(n) == object(x) and
                                   #(po, n) == #(po, x) and
                                   (po . n <= x') .

    -- rule 13
    eq assign<unlock(< a, n >) = action(a) == assign and
                                 action(n) == unlock and
                                 thread(a) == thread(n) .
    eq <store-n<write-n<(po, < x, x' >, < s, w >) = action(s) == store and
                                                    action(w) == write and
                                                    thread(s) == thread(w) and
                                                    thread(s) == thread(x) and
                                                    location(s) == location(w) and
                                                    location(s) == location(x) and
                                                    #(po, s) == #(po, w) .

    -- rule 14
    eq lock<use(< o, u >) = action(o) == lock and
                            action(u) == use and
                            thread(o) == thread(u) .
    eq <assign\l<-or-<read-n<load-n<(po, < x, x' >, < o/r, a/l >) =
         (action(a/l) == assign and o/r == x and
          thread(a/l) == thread(x') and
          location(a/l) == location(x') and
          (po . a <= x')) or
         (action(o/r) == read and action(a/l) == load and
          thread(o/r) == thread(a/l) and thread(o/r) == thread(x) and
          location(o/r) == location(a/l) and location(o/r) == location(x') and
          #(po, o/r) == #(po, a/l)) .

    -- rule 15
    eq lock<store(< o, s >) = action(o) == lock and
                              action(s) == store and
                              thread(o) == thread(s) .
    eq <assign\l<(po, < x, x' >, a) = action(a) == assign and
                                      thread(a) == thread(x') and
                                      location(a) == location(x') and
                                      (po . x <= a) and (po . a <= x') .
  }
}


make RULE1 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Pair<Action;Action>>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> fullrelation/1,
                         op exists-range -> singleton,
                         op all-pred -> samethread,
                         op ext-pred -> ext-adjoin,
                         op exists-pred -> ordered }])

make RULE2 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Pair<Action;Action>>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> fullrelation/1,
                         op exists-range -> singleton,
                         op all-pred -> samelocobj,
                         op ext-pred -> ext-adjoin,
                         op exists-pred -> ordered }])

make RULE3 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Pair<Action;Action>>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> relation,
                         op exists-range -> underlying,
                         op all-pred -> store<store,
                         op ext-pred -> ext-adjoin,
                         op exists-pred -> <assign< }])

make RULE4 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Pair<Action;Action>>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> relation,
                         op exists-range -> underlying,
                         op all-pred -> assign<load,
                         op ext-pred -> ext-adjoin,
                         op exists-pred -> <store< }])

make RULE5 (RULE[RULES { var x : AllRange,
                         sort AllRange -> Action,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Action>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> underlying,
                         op exists-range -> underlying,
                         op all-pred(x) -> use(x),
                         op ext-pred -> ext-in,
                         op exists-pred -> assign<-or-load< }])

make RULE6 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Pair<Action;Action>>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> relation,
                         op exists-range -> underlying,
                         op all-pred -> assign<load,
                         op ext-pred -> ext-adjoin,
                         op exists-pred -> <store< }])

make RULE7 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Pair<Action;Action>>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> relation,
                         op exists-range -> underlying,
                         op all-pred -> assign<store,
                         op ext-pred -> ext-adjoin,
                         op exists-pred -> <assign/v< }])

make RULE8 (RULE[RULES { var x : AllRange,
                         sort AllRange -> Action,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Action>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> underlying,
                         op exists-range -> underlying,
                         op all-pred(x) -> load(x),
                         op ext-pred -> ext-in,
                         op exists-pred -> read-n< }])

make RULE9 (RULE[RULES { var x : AllRange,
                         sort AllRange -> Action,
                         sort ExistsRange -> Action,
                         sort Set<AllRange> -> Set<Action>,
                         sort Set<ExistsRange> -> Set<Action>,
                         op all-range -> underlying,
                         op exists-range -> underlying,
                         op all-pred(x) -> write(x),
                         op ext-pred -> ext-in,
                         op exists-pred -> store-n< }])

make RULE10 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                          sort ExistsRange -> Pair<Action;Action>,
                          sort Set<AllRange> -> Set<Pair<Action;Action>>,
                          sort Set<ExistsRange> -> Set<Pair<Action;Action>>,
                          op all-range -> relation,
                          op exists-range -> relation,
                          op all-pred -> store-m<load-n,
                          op ext-pred -> ext-adjoin,
                          op exists-pred -> write-m<read-n }])

make RULE11 (RULE[RULES { var x : AllRange,
                          sort AllRange -> Action,
                          sort ExistsRange -> Action,
                          sort Set<AllRange> -> Set<Action>,
                          sort Set<ExistsRange> -> Set<Action>,
                          op all-range -> underlying,
                          op exists-range -> underlying,
                          op all-pred(x) -> unlock(x),
                          op ext-pred -> ext-in,
                          op exists-pred -> lock-n< }])

make RULE12 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                          sort ExistsRange -> Action,
                          sort Set<AllRange> -> Set<Pair<Action;Action>>,
                          sort Set<ExistsRange> -> Set<Action>,
                          op all-range -> relation,
                          op exists-range -> underlying,
                          op all-pred -> lock-n<lock,
                          op ext-pred -> ext-adjoin,
                          op exists-pred -> unlock-n< }])

make RULE13 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                          sort ExistsRange -> Pair<Action;Action>,
                          sort Set<AllRange> -> Set<Pair<Action;Action>>,
                          sort Set<ExistsRange> -> Set<Pair<Action;Action>>,
                          op all-range -> relation,
                          op exists-range -> relation,
                          op all-pred -> assign<unlock,
                          op ext-pred -> ext-adjoin,
                          op exists-pred -> <store-n<write-n< }])

make RULE14 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                          sort ExistsRange -> Pair<Action;Action>,
                          sort Set<AllRange> -> Set<Pair<Action;Action>>,
                          sort Set<ExistsRange> -> Set<Pair<Action;Action>>,
                          op all-range -> relation,
                          op exists-range -> relation,
                          op all-pred -> lock<use,
                          op ext-pred -> ext-adjoin,
                          op exists-pred -> <assign\l<-or-<read-n<load-n< }])

make RULE15 (RULE[RULES { sort AllRange -> Pair<Action;Action>,
                          sort ExistsRange -> Action,
                          sort Set<AllRange> -> Set<Pair<Action;Action>>,
                          sort Set<ExistsRange> -> Set<Action>,
                          op all-range -> relation,
                          op exists-range -> underlying,
                          op all-pred -> lock<store,
                          op ext-pred -> ext-adjoin,
                          op exists-pred -> <assign\l< }])



module! EVENTSPACE {
  imports {
    protecting (RULE1 * { op rule -> rule1, op rule-ext -> rule-ext1 })
    protecting (RULE2 * { op rule -> rule2, op rule-ext -> rule-ext2 })
    protecting (RULE3 * { op rule -> rule3, op rule-ext -> rule-ext3 })
    protecting (RULE4 * { op rule -> rule4, op rule-ext -> rule-ext4 })
    protecting (RULE5 * { op rule -> rule5, op rule-ext -> rule-ext5 })
    protecting (RULE6 * { op rule -> rule6, op rule-ext -> rule-ext6 })
    protecting (RULE7 * { op rule -> rule7, op rule-ext -> rule-ext7 })
    protecting (RULE8 * { op rule -> rule8, op rule-ext -> rule-ext8 })
    protecting (RULE9 * { op rule -> rule9, op rule-ext -> rule-ext9 })
    protecting (RULE10 * { op rule -> rule10, op rule-ext -> rule-ext10 })
    protecting (RULE11 * { op rule -> rule11, op rule-ext -> rule-ext11 })
    protecting (RULE12 * { op rule -> rule12, op rule-ext -> rule-ext12 })
    protecting (RULE13 * { op rule -> rule13, op rule-ext -> rule-ext13 })
    protecting (RULE14 * { op rule -> rule14, op rule-ext -> rule-ext14 })
    protecting (RULE15 * { op rule -> rule15, op rule-ext -> rule-ext15 })
  }

  signature {
    [ EventSpaceErr < PartialOrderErr<Action>,
      EventSpaceErr < EventSpace,
      EventSpaceOK < PartialOrderOK<Action>,
      EventSpaceOK < EventSpace,
      EventSpace < PartialOrder<Action> ]

    op bottom : -> EventSpaceErr { constr }
    op null : -> EventSpaceOK { constr }
    op (_+_) : EventSpaceOK Action -> EventSpaceOK { constr } -- shouldn't be used!!
    op (_+_) : EventSpace Action -> EventSpace { constr }
    op (_+_<_) : EventSpaceOK Action Action -> EventSpace { constr }
    op (_+_<_) : EventSpace Action Action -> EventSpace { constr }

    op _+<_ : EventSpaceOK Action -> EventSpace
    op _+<_ : EventSpace Action -> EventSpace
    op continuations : EventSpace -> Set<Action>

    op extend : EventSpace Action -> PartialOrder<Action>
    op extend< : PartialOrder<Action> Action Set<Action> -> PartialOrder<Action>
    op extend<wl : PartialOrder<Action> Action -> PartialOrder<Action>
    op extend<wl : PartialOrder<Action> Action Set<Action> -> PartialOrder<Action>
    op eventspace : PartialOrder<Action> -> EventSpace
    op eventspace-ext : PartialOrder<Action> Action -> EventSpace
    op po2es : PartialOrder<Action> -> EventSpace
  }

  axioms {
    var es : EventSpace
    var po : PartialOrder<Action>
    vars x x' x'' r l u w s s' a o o' n : Action
    var mx : Set<Action>
    vars p p' : Pair<Action;Action>
    var mp : Set<Pair<Action;Action>>

    eq es +< x = eventspace-ext(extend(es, x), x) .

    eq extend(bottom, x) = (bottom):EventSpaceErr .
    eq extend(es, x) = extend<wl(extend<(es + x, x, underlying(es)), x) .
    eq extend<(po, x, empty) = po .
    eq extend<(po, x, x' mx) = if (threadaction(x) and threadaction(x') and
                                   thread(x) == thread(x')) or
                                  (memoryaction(x) and memoryaction(x') and
                                   location(x) == location(x'))
                               then extend<(po + x' < x, x, mx)
                               else extend<(po, x, mx)
                               fi .
    eq extend<wl(po, x) = if action(x) == load or action(x) == write
                          then extend<wl(po, x, underlying(po))
                          else po
                          fi .
    eq extend<wl(po, x, empty) = po .
    eq extend<wl(po, x, x' mx) = if (action(x) == load and action(x') == read) or
                                    (action(x) == write and action(x') == store)
                                 then extend<wl(po + x' < x, x, mx)
                                 else extend<wl(po, x, mx)
                                 fi .

    eq eventspace(po) = if (po =/= ((bottom):PartialOrderErr<Action>) and
                            rule1(po) and rule2(po) and
                            rule3(po) and rule4(po) and
                            rule5(po) and rule6(po) and
                            rule7(po) and rule8(po) and
                            rule9(po) and rule10(po) and
                            rule11(po) and rule12(po) and
                            rule13(po) and rule14(po) and
                            rule15(po))
                        then po2es(po)
                        else ((bottom):EventSpaceErr)
                        fi .

    eq eventspace-ext(po, x) = if (po =/= ((bottom):PartialOrderErr<Action>) and
                                   rule-ext1(po, x) and rule-ext2(po, x) and
                                   rule-ext3(po, x) and rule-ext4(po, x) and
                                   rule-ext5(po, x) and rule-ext6(po, x) and
                                   rule-ext7(po, x) and rule-ext8(po, x) and
                                   rule-ext9(po, x) and rule-ext10(po, x) and
                                   rule-ext11(po, x) and rule-ext12(po, x) and
                                   rule-ext13(po, x) and rule-ext14(po, x) and
                                   rule-ext15(po, x))
                               then po2es(po)
                               else ((bottom):EventSpaceErr)
                               fi .

    eq po2es((null):PartialOrderOK<Action>) = null .
    eq po2es(po + x) = po2es(po) + x .
    eq po2es(po + x < x') = po2es(po) + x < x' .
  }
}

eof
