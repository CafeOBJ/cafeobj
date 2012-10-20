** -*- Mode: CafeOBJ -*-
--> Unification: tlanslated from OBJ3 example unify.obj

require tiny-list

module! TERM 
     principal-sort Term
{
  protecting (QID)
  [ Id < Term ]
}

module! EQN 
     principal-sort Eqn
{
  [ Eqn ]
}

module! SUBST {
  imports {
    pr (LIST[TERM] * { sort List -> TermList,
		       sort NeList -> NeTermList })

    pr (LIST[EQN] * { sort List -> System,
		      sort NeList -> NeSystem, 
		      op nil -> null,
		      op (__) -> (_&_) })

    using (QID * { sort Id -> Op })
  }

  signature {

    op _[_] : Op TermList -> Term {prec: 1}
    op _=_ : Term Term -> Eqn {comm prec: 120}
    op {_} : System -> System    ** scope delimiter
    op _=_ : TermList TermList -> System {comm prec: 120}
  }

  signature {
    op let_be_in_ : Id Term Term -> Term 
    op let_be_in_ : Id Term TermList -> TermList 
    op let_be_in_ : Id Term Eqn -> Eqn 
    op let_be_in_ : Id Term System -> System 
  }

  axioms {
    vars T U V : Term    var Us : NeTermList 
    var S : NeSystem     var Ts : TermList 
    vars X Y : Id      var F : Op 
    -- ----------------------------------------
    eq (T Ts = U Us) = (T = U) & (Ts = Us).
    eq let X be T in nil = nil .
    eq let X be T in Y = if X == Y then T else Y fi .
    eq let X be T in F[Ts] = F[let X be T in Ts].
    eq let X be T in (U Us) = (let X be T in U) (let X be T in Us).
    eq let X be T in (U = V) = (let X be T in U) = (let X be T in V) .
    eq let X be T in null = null .
    eq let X be T in ((U = V) & S) = (let X be T in (U = V)) & (let X be T in S).
  }
}


**> first without occur check
module! UNIFY {
  imports {
    using (SUBST)
  }
  signature {
    op unify_ : System -> System {prec: 120}
    op fail : -> Eqn 
  }

  axioms {
    var T : Term             vars Ts Us : NeTermList 
    vars S S' S'' : System   var X : Id 
    -- -------------------------------------------
    eq unify S = {{S}} .
    eq S & (T = T) & S' = S & S' .
    eq S & fail & S' = fail .
    eq let X be T in fail = fail .
    eq {null} = null .
    eq {fail} = fail .
    -- -------------------------------------------
    vars F G : Op    var X : Id 
    -- -------------------------------------------
    eq {S & (F[Ts] = G[Us]) & S'} = if F == G and | Ts | == | Us |
      then {S & (Ts = Us) & S'} else fail fi .
    eq {S & {S' & (X = T) & S''}} = if X == T then {S & {S' & S''}} else
      {(X = T) & (let X be T in S) & {let X be T in S' & S''}} fi .
  }
}

select UNIFY
reduce unify 'f['g['X] 'Y] = 'f['g['h['Y]] 'h['Z]].
reduce unify 'f['X 'Y] = 'f['Y 'g['Y]].
reduce unify ('f['g['X] 'Y] = 'f['g['h['Y]] 'h['Z]]) & ('h['X] = 'Z).
reduce unify 'f['X 'g['Y]] = 'f['Z 'Z].
reduce unify 'f['X 'g['Y]] = 'f['Z].
reduce unify 'f['Y 'g['Y]] = 'f['h['Z] 'Z].
reduce unify 'f['Y 'a[nil]] = 'f['g['a[nil]] 'Z].

**> now add occur check
module! UNIFY-OCH {
  using (UNIFY)
  op _in_ : Id TermList -> Bool 
  vars X Y : Id    var F : Op 
  var T : Term     var Ts : NeTermList 
  eq X in Y = X == Y .
  eq X in F[Ts] = X in Ts .
  eq X in T Ts = X in T or X in Ts .
  cq (X = T) = fail if X in T .
}

select UNIFY-OCH
reduce unify 'f['g['X] 'Y] = 'f['g['h['Y]] 'h['Z]].
reduce unify 'f['X 'Y] = 'f['Y 'g['Y]].
reduce unify ('f['g['X] 'Y] = 'f['g['h['Y]] 'h['Z]]) & ('h['X] = 'Z).
reduce unify 'f['X 'g['Y]] = 'f['Z 'Z].
reduce unify 'f['X 'g['Y]] = 'f['Z].
reduce unify 'f['Y 'g['Y]] = 'f['h['Z] 'Z].
reduce unify 'f['Y 'a[nil]] = 'f['g['a[nil]] 'Z].
--
eof
--
$Id: unify.mod,v 1.1.1.1 2003-06-19 08:30:18 sawada Exp $
