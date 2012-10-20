-- From: Hiroshi Ishikawa <h-ishika@jaist.ac.jp>
-- Date: Mon, 6 Oct 97 18:21:23 JST
-- Message-Id: <9710060921.AA00543@copper.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject: Example file.
-- Content-Type: text
-- Content-Length: 35934

-- 石川です．

-- 遅くなりましたが，リダクションに長時間を要するサンプルをお送りします．
-- 以下の例題は，CafeOBJ version 1.3.b7 (Linux version) で実行し，
--  3.910 sec for parse, 
--  443582 rewrites(9444.530 sec), 
--  1541928 match attempts
-- ほどかかって正しい結果を返してきました．

-- しかし，CafeOBJ 1.3.1(1.4.0(Beta-1)の直前の版) および 1.4.0(Beta-1)では，
-- 書き換え途中で term が壊れてしまうという現象が生じます．

-- op _[_] : Id TermList -> Term

-- で prolog の複合項を定義し，

-- pred _belongsto_ : Term TermList

-- を使って，述語名が与えられたリストに存在するか否かをチェックさせているので
-- すが，G = 'test [ nil ] , GL = nil として，書き換え規則

-- trans
--   < P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >
--   =>
--   if (C in EL)
--   then (if G belongsto ( 'fork , 'new-cell , 'push , 'assert , 'cv-write ,
--                          'cv-take , 'cv-set , 'cv-ref , 'subst-cell , 
--                          'cv-read , 'die )
--        then < P @@ Process | EL % Meta % << C ; M ; N >> % G , GL % CTRL >
--        else < P @@ Process | EL % << C ; M ; N >> % NoLoc % G , GL % CTRL >
--        fi)
--   else (if CTRL =/= Empty
--        then < P @ Process | EL % snd( head( CTRL ) ) %
--                                  fst( head( CTRL ) ) % tail( CTRL ) >
--        else [< P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >]
--        fi)
--   fi .

-- を適用した時，右辺の G には 'test [ nil ] ではなく 'test のみが代入されて
-- います．

-- また，

-- -- fork.
-- [Warning]: axiom : < C @ Cell | CVS % CLS > < P @@ Process | EL %
--                 Meta % BL % ('fork [ TL ] , GL) % CTRL > => < C @
--                 Cell | CVS % (('process [ create-pid(TL,CVS) ] :=
--                 True) CLS) > (< create-pid(TL,CVS) @ Process | EL 
--                % (<< nthe(1,EL) ; 1 ; 1 >>) % TL % Empty > < P @ 
--                Process | EL % BL % GL % CTRL >) if C == 'system-cell
--            contains error operators, should be used with care!..
-- -- done.
-- -- new-cell.
-- [Warning]: axiom : < 'system-cell @ Cell | CVS % CLS > < P @@ Process 
--                | EL % Meta % BL % ('new-cell [ (T , TL) ] , GL) %
--                 CTRL > => if (cell-exists(T,CLS) == false) then (
--                < 'system-cell @ Cell | CVS % (('cell [ T ] := True)
--                 CLS) > (< T @ Cell | create-cvpairs(TL) % NoClause 
--                > < P @ Process | EL % BL % GL % CTRL >)) else (< 
--                'system-cell @ Cell | CVS % CLS > [ < P @ Process 
--                | EL % BL % ('new-cell [ (T , TL) ] , GL) % CTRL >
--                 ]) fi
--            contains error operators, should be used with care!..
-- -- done.
-- -- push.
-- [Warning]: axiom : < 'system-cell @ Cell | CVS % CLS > < P @@ Process 
--                | EL % Meta % (<< C ; M ; N >>) % ('push [ T ] , GL)
--                 % CTRL > => if cell-exists(T,CLS) then (< 'system-cell 
--                @ Cell | CVS % CLS > < P @ Process | (T EL) % (<< 
--                T ; 1 ; 1 >>) % GL % CTRL >) else (< 'system-cell 
--                @ Cell | CVS % CLS > < P @@ Process | EL % Meta % 
--                (<< C ; M ; N >>) % ('push [ T ] , GL) % CTRL >) fi
               
--            contains error operators, should be used with care!..

-- という Warning が出力されるようになりました．

-- -- ----->8----->8----->8----->8----->8----->8----->8----->8----->8
--
-- file name : gaea.mod
--  sep 15 1997
--   fast versiton
--

-- include built-in module
require tiny-list

--
-- tentative
--
module DEFAULT ( X :: TRIV ) {
  [ Elt ]

  op default : -> Elt
}

--
-- module TERM
--
module TERM {
  protecting(QID)
  protecting(NAT)
  [ Id Nat < Term ]
}

--
-- module TERMLIST
--
module TERMLIST {
  imports{
    extending( (LIST * { sort NeList -> NeTermList ,
                         sort List -> TermList ,
                         op (__) -> (_,_) }) [TERM] )
    protecting( (DEFAULT * { op default -> True }) [TERM])
  }

  signature{
    op ! : -> Term
    op fail : -> Term 
    op nl : -> Term 
    op _<-_ : Term Term -> Term
--    op [_] : TermList -> Term
--    op [_|_] : TermList Term -> Term
--    op _[_] : Op TermList -> Term { prec: 1 }
    op _[_] : Id TermList -> Term { prec: 1 }
    op functor : Term -> Id
    op argument : Term -> TermList
    pred _belongsto_ : Term TermList
    pred _belongsto0_ : Term TermList
  }

  axioms{
    var F : Id   vars TL TL' : TermList
    vars T T' : Term

--    eq functor( ! ) = ! .
--    eq functor( fail ) = 'fail .
--    eq functor( nl ) = 'nl .
--    eq functor( 'fail ) = 'fail .
--    eq functor( 'nl ) = 'nl .
    eq functor( F [ TL ] ) = F .
    eq argument( F [ TL ] ) = TL .

    eq T belongsto nil = false .
    eq T belongsto ( T' , TL ) = if functor( T ) == T'
                                 then true else (T belongsto0 T' , TL) fi .
    eq T belongsto0 ( T' , TL )
       = if T == T' then true else (T belongsto TL) fi .

  }
}

-- ------------------------- ref. unify.mod ---------------------------
--
-- Unification : translated from OBJ3 example unify.obj
--
module EQN {
  signature{
    [ Eqn ]
  }
}

module SUBST {
  imports{
    protecting (TERMLIST)
    protecting ((LIST * { sort List -> System ,
                          sort NeList -> NeSystem ,
                          op nil -> null ,
                          op (__) -> (_&_) }) [EQN])
  }

  signature{
    op _=_ : Term Term -> Eqn { comm prec: 120 }
    op {_} : System -> System     ** scope delimiter
    op _=_ : TermList TermList -> System { comm prec: 120 }
    op let_be_in_ : Id Term Term -> Term
    op let_be_in_ : Id Term TermList -> TermList
    op let_be_in_ : Id Term Eqn -> Eqn
    op let_be_in_ : Id Term System -> System

  }

  axioms{
    vars T U V : Term  var Us : NeTermList
    var S : NeSystem   var Ts : TermList

    eq (T , Ts = U , Us) = (T = U) & (Ts = Us) .

    vars F X Y : Id

    eq let X be T in nil = nil .
--    eq let X be T in Y = if X == Y then T else Y fi .
    eq let X be T in V = if X == V then T else V fi .
    eq let X be T in F[Ts] = F[ let X be T in Ts ] .
    eq let X be T in (U , Us) = (let X be T in U) , (let X be T in Us) .
    eq let X be T in (U = V) = (let X be T in U) = (let X be T in V) .
    eq let X be T in null = null .
    eq let X be T in ((U = V) & S) = (let X be T in (U = V)) & (let X be T in S) .

  }
}

module UNIFY {
  imports{
    using (SUBST)
  }

  signature{
    op unify_ : System -> System { prec: 120 }
    op failure : -> Eqn
  }

  axioms{
    var T : Term            vars Ts Us : NeTermList
    vars S S' S'' : System  var X : Id
    vars F G : Id
    vars M N : Nat

    eq unify S = {{S}} .
    eq S & (T = True) & S' = S & S' .
    eq S & (M = N) & S' = if M == N then S & S' else failure fi .
    eq S & (T = T) & S' = S & S' .
    eq S & failure & S' = failure .
    eq let X be T in failure = failure .
    eq {null} = null .
    eq {failure} = failure .

    eq {S & (F [nil] = G [nil]) & S'} =
       if F == G
       then {S & S'}
       else failure fi .

--    eq {S & (F = G [nil]) & S'} = if F == G then { S & S' } else failure fi .

--    eq {S & (F = G [nil]) & S'} = if F == G
--                                  then { S & S' }
--                                  else { (F = G [nil]) & 
--                                       { let F be G [ nil ] in S & S' } }
--                                  fi .

    eq {S & (F [Ts] = G [nil]) & S'} = failure .

    cq {S & (F [nil] = T) & S'} = failure if T == ! or T == fail or T == nl .
    cq {S & (F [Ts] = T) & S'} = failure if T == ! or T == fail or T == nl .

-- patch -------------------------------------------
    eq {S & ('name [Ts] = 'name [Us]) & S'} =
       if | Ts | == | Us |
       then {S & (Us = Ts) & S'}
       else failure fi .
-- -------------------------------------------

    eq {S & (F [Ts] = G [Us]) & S'} =
       if F == G and | Ts | == | Us |
       then {S & (Ts = Us) & S'}
       else failure fi .

    eq {S & {S' & (X = T) & S''}} =
       if (T == ! or T == fail or T == nl) then failure else
       if X == T
       then {S & {S' & S''}}
       else {(X = T) & (let X be T in S) & {let X be T in S' & S''}} fi fi .

  }
}

-- module UNIFY-OCH {
--  using (UNIFY)
--  pred _in_ : Id TermList
--  vars X Y : Id    var F : Id
--  var T : Term     var Ts : NeTermList 
--  eq X in Y = X == Y .
--  eq X in F[nil] = false .
--  eq X in F[Ts] = X in Ts .
--  eq X in (T , Ts) = X in T or X in Ts .
--  cq (X = T) = failure if X in T .
-- }
-- ------------------------- ref. unify.mod ---------------------------

--
-- module SUBST-TERM
--
module SUBST-TERM {
  imports{
    protecting(UNIFY)
--    protecting(UNIFY-OCH)
  }

  signature{
    op subst : System TermList -> TermList
    op subst-main : Eqn TermList -> TermList
  }

  axioms{
    vars S S' : System vars T Y : Term
    vars F X : Id vars TL TL' : TermList

    eq subst( null , TL ) = TL .
    eq subst( {(X = Y) & S'} , TL ) = subst( {S'} ,
                                      subst-main( (X = Y) , TL ) ) .

    eq subst-main( (X = Y) , nil ) = nil .
    eq subst-main( (X = Y) , ( F [ TL' ] , TL) ) =
         F [ subst-main( (X = Y) , TL' ) ] , subst-main( (X = Y) , TL ) .

    eq subst-main( X = Y  , (T , TL) ) =
         if X == T
         then (Y , subst-main( X = Y , TL ))
         else (T , subst-main( X = Y , TL ))
         fi .

  }
}

--
-- module CLAUSE
-- 
module CLAUSE {
  signature{
    [ Clause ]
  }
}

--
-- module CLAUSELIST
--
module CLAUSELIST {
  imports{
    protecting(TERMLIST)
    protecting( (LIST * { sort NeList -> NeClauseList ,
                          sort List -> ClauseList ,
                          op nil -> NoClause } ) [CLAUSE])
    protecting( (DEFAULT * { op default -> ClError }) [CLAUSE])
  }

  signature{
    op (_:_) : Term TermList -> Clause { prec: 15 }
    op (_:=_) : Term TermList -> Clause { prec: 15 }
    op (_:_:=_) : Term TermList TermList -> Clause { prec: 15 }

    op head-part : Clause -> Term
    op body-part : Clause -> TermList
    op nthcl : Nat ClauseList -> Clause
    op nthclsub : Nat Nat ClauseList -> Clause
    pred cell-exists : Term ClauseList
    pred process-exists : Term ClauseList
    op process-delete : Term ClauseList -> ClauseList
  }

  axioms {
    vars T T' : Term    vars TL TL' : TermList
    var C : Clause  var CLS : ClauseList
    vars M N : Nat
    var F : Id

    eq head-part( T : TL ) = T .
    eq body-part( T : TL ) = TL .

    eq head-part( T := TL ) = T .
    eq body-part( T := TL ) = ! , TL .

    eq head-part( T : TL := TL' ) = T .
    eq body-part( T : TL := TL' ) = TL , ! , TL' .

    eq nthcl( N , CLS ) = nthclsub( N , 1 , CLS ) .
    eq nthclsub( M , N , NoClause ) = ClError .
    eq nthclsub( N , N , C CLS ) = C .
    cq nthclsub( M , N , C CLS ) = nthclsub( M , N + 1 , CLS ) if M > N .

    eq cell-exists( T , NoClause ) = false .
    eq cell-exists( T , ('process [ T' ] := True) CLS ) =
         cell-exists( T , CLS ) .
    eq cell-exists( T , ('cell [ T' ] := True) CLS ) =
         if T == T'
         then true
         else cell-exists( T , CLS ) fi .

    eq process-exists( T , NoClause ) = false .
    eq process-exists( T , ('cell [ T' ] := True) CLS ) =
         process-exists( T , CLS ) .
    eq process-exists( T , ('process [ T' ] := True) CLS ) =
         if T == T'
         then true
         else process-exists( T , CLS ) fi .

    eq process-delete( T , NoClause ) = NoClause .
    eq process-delete( T , ( F [ T' ] := True ) CLS ) =
         if F == 'process and T == T'
         then CLS
         else ( F [ T' ] := True ) process-delete( T , CLS )
         fi .
  }
}

--
-- module ENV
--
-- module ENV {
--  imports{
--    protecting(QID)
--  }

--  signature{
--    [ Id < Name ]
--  }

--  signature{
--    [ Id ]
--  }
-- }

--
-- module LOC
--
module LOC {
  imports{
--    protecting( (3TUPLE * { sort 3Tuple -> Loc }) [ENV,NAT,NAT])
    protecting( (3TUPLE * { sort 3Tuple -> Loc }) [QID,NAT,NAT])
  }

  signature{
    op NoLoc : -> Loc
    op Meta : -> Loc
  }
}

--
-- module CONTROL
--
module CONTROL {
  imports{
    protecting(TERMLIST)
    protecting(LOC)
  }

  signature{
    [ Control ]
    op <<_;_>> : TermList Loc -> Control
    op fst : Control -> TermList
    op snd : Control -> Loc
  }

  axioms{
    var TL : TermList var L : Loc

    eq fst( << TL ; L >> ) = TL .
    eq snd( << TL ; L >> ) = L .
  }
}

--
-- module CVPAIR
--
module CVPAIR {
  imports{
    protecting( (2TUPLE * { sort 2Tuple -> CVPair }) [TERM,TERM])
  }
}

--
-- CVPAIRLIST
--
module CVPAIRLIST {
  imports{
    protecting(CVPAIR)
    protecting(TERMLIST)
  }

  signature{
    [ CVPair < CVPairList ]

    op undef : -> Term
    op NoCVPair : -> CVPairList
    op __ : CVPairList CVPairList -> CVPairList { assoc comm id: NoCVPair }
    op create-cvpairs : TermList -> CVPairList
    pred cv-exists : Term CVPairList
    op write-value : Term Term CVPairList -> CVPairList
    op get-value : Term CVPairList -> Term
    op reset-value : Term CVPairList -> CVPairList
    -- sfst.mod only
    op create-pid : Term CVPairList -> Id

  }

  axioms{
    vars T T' V U : Term    var TL : TermList
    var CVS : CVPairList
    var P : Id var     N : Nat

    eq create-cvpairs( nil )= NoCVPair .
    eq create-cvpairs( (T <- U) , TL ) = << T ; U >> create-cvpairs( TL ) .
    eq create-cvpairs( T , TL ) = << T ; undef >> create-cvpairs( TL ) .

    eq cv-exists( T , NoCVPair ) = false .
    eq cv-exists( T , << T' ; U >> CVS ) =
        if T == T' then true else cv-exists( T , CVS ) fi .

    eq get-value( T , << T' ; V >> CVS ) =
         if T == T' 
         then V
         else get-value( T , CVS )
         fi .

    eq write-value( T , V , << T' ; U >> CVS ) =
         if T == T'
         then << T' ; V >> CVS 
         else << T' ; U >> write-value( T , V , CVS ) 
         fi .

    eq reset-value( T , << T' ; V >> CVS ) =
         if T == T' 
         then << T' ; undef >> CVS
         else << T' ; V >> reset-value( T , CVS )
         fi .

    -- sfst.mod only
    eq create-pid( 'agent [ T , N ] , << T' ; P >> CVS ) =
       if T == T'
       then P
       else create-pid( 'agent [ T , N ] , CVS )
       fi .

  }
}

--
-- module CONTROLLIST
--
module CONTROLLIST {
  imports{
    protecting(CONTROL)
  }

  signature{
    [ Control < ControlList ]
    op Empty : -> ControlList
    op __ : ControlList ControlList -> ControlList { assoc id: Empty prec: 9 }
    op head_ : ControlList -> Control { prec: 120 }
    op tail_ : ControlList -> ControlList { prec: 120 }
    op assert-inc : Id ControlList -> ControlList
  }

  axioms{
    var C : Control   var CTRL : ControlList
    vars E E' : Id   vars M N : Nat
    var TL : TermList

    eq head C CTRL = C .
    eq tail C CTRL = CTRL .

    eq assert-inc( E , Empty ) = Empty .
    eq assert-inc( E , (<< TL ; (<< E' ; M ; N >>) >>) CTRL ) =
         if E == E'
         then (<< TL ; (<< E' ; M ; N + 1 >>) >>) assert-inc( E , CTRL )
         else (<< TL ; (<< E' ; M ; N >>) >>) assert-inc( E , CTRL )
         fi .
  }
}

--
-- ENVLIST
--
module ENVLIST {
  imports{
    protecting ( (LIST * { sort List -> EnvList ,
                           sort NeList -> NeEnvList , 
                           op nil -> NoEnv })[QID])
    protecting ( (DEFAULT * { op default -> EnvError })[QID])
  }

  signature{
    [ Id < EnvList ]

    pred _in_ : Id EnvList

    op nthe : Nat EnvList -> Id
    op nthesub : Nat Nat EnvList -> Id
    op subst-cell : Id Id EnvList -> EnvList
  }

  axioms{
    vars E E' : Id var EL : EnvList
    vars M N : Nat
    vars Old New : Id

    eq E in NoEnv = false .
    eq E in ( E' EL ) = if E == E' then true else (E in EL) fi .

    eq nthe( N , EL ) = nthesub( N , 1 , EL ) .
    eq nthesub( M , N , NoEnv ) = EnvError .
    eq nthesub( N , N , (E EL) ) = E .
    cq nthesub( M , N , (E EL) ) = nthesub( M , N + 1 , EL ) if M > N .

    eq subst-cell( Old , New , NoEnv ) = NoEnv .
    eq subst-cell( Old , New , (E EL) ) =
         if Old == E
         then ( New  EL )
         else (E  subst-cell( Old , New , EL ))
         fi .

  }
}

--
-- module STATES
--
module STATES {
  imports{
    protecting(CLAUSELIST)
    protecting(CONTROLLIST)
    protecting(CVPAIRLIST)
    protecting(ENVLIST)
    protecting(LOC)
    protecting(SUBST-TERM)
  }

  signature{
    [ Id < Flag ]
    [ Class ]
    [ Object < State ]


    op (<_@_|_%_>) : Id Class CVPairList ClauseList -> Object { prec: 0 }
    op (<_@_|_%_%_%_>) : Id Class EnvList Loc TermList ControlList
                          -> Object { prec: 0 }
    op ([<_@_|_%_%_%_>]) : Id Class EnvList Loc TermList ControlList
                          -> Object { prec: 0 }
    op (<_@@_|_%_%_%_%_>) : Id Class EnvList Loc Loc TermList ControlList
                           -> Object { prec: 0 }
    op ([<_@@_|_%_%_%_%_>]) : Id Class EnvList Loc Loc TermList ControlList
                           -> Object { prec: 0 }

    op Cell : -> Class
    op Process : -> Class
    op __ : State State -> State { assoc comm }
  }

  axioms{
    vars E C P : Id
    var CV : Id
    vars Old New : Id
    vars CVS CVS' : CVPairList
    vars CLS CLS' : ClauseList
    var EL : EnvList
    vars L BL : Loc
    var CTRL : ControlList
    vars V T T' G : Term
    vars GL TL TL' : TermList
    vars M N : Nat

--
-- built-in predicates
--
trans
  < P @ Process | EL % << C ; M ; N >> % True , GL % CTRL >
  =>
  < P @ Process | EL % << C ; M ; N >> % GL % CTRL > .

--> cut
trans
  < P @ Process | EL % << C ; M ; N >> % ! , GL % CTRL >
  =>
  if CTRL =/= Empty
  then < P @ Process | EL % << C ; M ; N >> % GL % tail( CTRL ) >
  else < P @ Process | EL % << C ; M ; N >> % GL % CTRL >
  fi .
--> done

--> fail
trans
  < P @ Process | EL % BL % fail , GL % CTRL >
  => 
  if CTRL =/= Empty
  then < P @ Process | EL % snd( head( CTRL ) ) %
                            fst( head( CTRL ) ) % tail( CTRL ) >
  else [< P @ Process | EL % BL % fail , GL % CTRL >]
  fi .
--> done
--

-- write
--   for debug
--
--> write
trans
  < 'display @ Cell | CVS % CLS >
  < P @ Process | EL % BL % 'write [ T ] , GL % CTRL >
  =>
  < 'display @ Cell | CVS % ('write [ T ] : True) CLS >
  < P @ Process | EL % BL % GL % CTRL > .
--> done

--
-- nl
--   for debug
--
--> nl rule 
trans
  < 'display @ Cell | CVS % CLS >
  < P @ Process | EL % BL % nl , GL % CTRL >
  =>
  < 'display @ Cell | CVS % (nl : True) CLS >
  < P @ Process | EL % BL % GL % CTRL > .
--> done

--
-- add
--
--> add
trans
  < P @ Process | EL % BL % 'add [ M , N , T' ] , GL % CTRL >
  =>
  < P @ Process | EL % BL % subst( { T' =  M + N } , GL ) % CTRL > .
--> done

--
-- eq
--
trans
  < P @ Process | EL % BL % 'eq [ T , T' ] , GL % CTRL >
  =>
  if (unify (T = T')) =/= failure
  then < P @ Process | EL % BL % subst( (unify (T = T')) , GL ) % CTRL >
  else (if CTRL =/= Empty
       then < P @ Process | EL % snd( head( CTRL ) ) % fst( head( CTRL ) ) %
                            tail( CTRL ) >
       else [< P @ Process | EL % BL % 'eq [ T , T' ] , GL % CTRL >]
       fi)
  fi .
--> done

--
-- for some reason, this rule are applied.
--
--> classification rule
trans
  < P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >
  =>
  if (C in EL)
  then (if G belongsto ( 'fork , 'new-cell , 'push , 'assert , 'cv-write ,
                         'cv-take , 'cv-set , 'cv-ref , 'subst-cell , 
                         'cv-read , 'die )
       then < P @@ Process | EL % Meta % << C ; M ; N >> % G , GL % CTRL >
       else < P @@ Process | EL % << C ; M ; N >> % NoLoc % G , GL % CTRL >
       fi)
  else (if CTRL =/= Empty
       then < P @ Process | EL % snd( head( CTRL ) ) %
                                 fst( head( CTRL ) ) % tail( CTRL ) >
       else [< P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >]
       fi)
  fi .
--> done

-- trans
--  < P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >
--  =>
--  if (C in EL)
--  then (if G belongsto ( 'write , nl , 'add )
--       then < P @@ Process | EL % << C ; M ; N >> % << C ; M ; N >> % G , GL % CTRL >
--       else (if G belongsto ( 'fork , 'new-cell , 'push , 'assert , 'cv-write ,
--                              'cv-take , 'cv-set , 'cv-ref , 'subst-cell , 'cv-read )
--            then < P @@ Process | EL % << C ; M ; N >> % << C ; M ; N >>
--                                     % G , GL % CTRL >
--            else < P @@ Process | EL % << C ; M ; N >> % NoLoc % G , GL % CTRL >
--            fi)
--       fi)
--  else [< P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >]
--  fi .
--> done.

--
-- user define
--
--> main rule
trans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % << C ; M ; N >> % BL % G , GL % CTRL >
  =>
  if BL == NoLoc
  then
  (if (C in EL)
  then (if nthcl( N , CLS ) =/= ClError
       then (if (unify head-part( nthcl( N , CLS ) ) = G) =/= failure
            then < C @ Cell | CVS % CLS >
                 < P @ Process | EL % << nthe( 1 , EL ) ; 1 ; 1 >> %
                                 subst((unify head-part( nthcl( N , CLS ) ) = G),
                                        (body-part( nthcl( N , CLS ) ) , GL) ) %
                                 (<< G , GL ; << C ; M ; N + 1 >> >>) CTRL >
            else < C @ Cell | CVS % CLS >
                 < P @@ Process | EL % << C ; M ; N + 1 >> % BL % G , GL % CTRL >
            fi)
       else (if nthe( M + 1 , EL ) =/= EnvError
            then < C @ Cell | CVS % CLS >
                 < P @@ Process | EL % << nthe( M + 1 , EL ) ; M + 1 ; 1 >> %
                                  BL % G , GL % CTRL >
            else (if CTRL =/= Empty
                 then < C @ Cell | CVS % CLS >
                      < P @ Process | EL % snd( head( CTRL ) ) %
                                      fst( head( CTRL ) ) % tail( CTRL ) >
                 else < C @ Cell | CVS % CLS >
                      [< P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >]
                 fi)
            fi)
       fi)
  else (if CTRL =/= Empty
       then < C @ Cell | CVS % CLS >
            < P @ Process | EL % snd( head( CTRL ) ) %
                                 fst( head( CTRL ) ) % tail( CTRL ) >
       else < C @ Cell | CVS % CLS >
            [< P @ Process | EL % BL % G , GL % CTRL >]
       fi)
  fi)
  else
  (if (C in EL)
  then (if nthcl( N , CLS ) =/= ClError
       then (if (unify head-part( nthcl( N , CLS ) ) = G) =/= failure
            then < C @ Cell | CVS % CLS >
                 < P @ Process | EL % << nthe( 1 , EL ) ; 1 ; 1 >> %
                                 subst((unify head-part( nthcl( N , CLS ) ) = G),
                                       (body-part( nthcl( N , CLS ) ) , GL) ) %
                                 (<< G , GL ; << C ; M ; N + 1 >> >>) CTRL >
            else < C @ Cell | CVS % CLS >
                 < P @@ Process | EL % << C ; M ; N + 1 >> % BL % G , GL % CTRL >
            fi)
       else (if nthe( M + 1 , EL ) =/= EnvError
            then < C @ Cell | CVS % CLS >
                 < P @@ Process | EL % << nthe( M + 1 , EL ) ; M + 1 ; 1 >> %
                                  BL % G , GL % CTRL >
            else < C @ Cell | CVS % CLS >
                 < P @@ Process | EL % Meta % BL % G , GL % CTRL >
            fi)
       fi)
  else (if CTRL =/= Empty
       then < C @ Cell | CVS % CLS >
            < P @ Process | EL % snd( head( CTRL ) ) %
                                 fst( head( CTRL ) ) % tail( CTRL ) >
       else < C @ Cell | CVS % CLS >
            [< P @ Process | EL % BL % G , GL % CTRL >]
       fi)
  fi)
  fi .
--  else < C @ Cell | CVS % CLS >
--       [< P @ Process | EL % << C ; M ; N >> % G , GL % CTRL >]
--> done.
-- ----------------------------------------------------------------------

--
-- fork
--
--> fork
ctrans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'fork [ TL ] , GL % CTRL >
  =>
  < C @ Cell | CVS % ('process [ create-pid( TL , CVS ) ] := True) CLS >
  < create-pid( TL , CVS ) @ Process | EL % << nthe( 1 , EL ) ; 1 ; 1 >> % 
                                       TL % Empty >
  < P @ Process | EL % BL % GL % CTRL > if C == 'system-cell .
--> done

--
-- new-cell
--
--> new-cell
trans
  < 'system-cell @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % ('new-cell [ T , TL ] , GL) % CTRL >
  =>
  if cell-exists( T , CLS ) == false
  then < 'system-cell @ Cell | CVS % ('cell [ T ] := True) CLS >
       < T @ Cell | create-cvpairs( TL ) % NoClause >
       < P @ Process | EL % BL % GL % CTRL >
  else < 'system-cell @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % ('new-cell [ T , TL ] , GL) % CTRL >]
  fi .
--> done

--
-- push/1
--
--> push
trans
  < 'system-cell @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % << C ; M ; N >> % 'push [ T ] , GL % CTRL >
  => 
  if cell-exists( T , CLS )
  then < 'system-cell @ Cell | CVS % CLS >
       < P @ Process | (T  EL) % << T ; 1 ; 1 >> % GL % CTRL >
  else < 'system-cell @ Cell | CVS % CLS >
       < P @@ Process | EL % Meta % << C ; M ; N >> % 'push [ T ] , GL % CTRL >
  fi .
--> done

--
-- assert
--
--> assert
ctrans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'assert [ T ] , GL % CTRL >
  =>
  < C @ Cell | CVS % ( T : True ) CLS >
  < P @ Process | EL % BL % GL % assert-inc( C , CTRL ) >
  if nthe( 1 , EL ) == C .
--> done

--
-- cv-write
--
--> cv-write
trans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'cv-write [ C , CV , V ] , GL % CTRL >
  =>
  if cv-exists( CV , CVS )
  then (if get-value( CV , CVS ) == undef
       then < C @ Cell | write-value( CV , V , CVS ) % CLS >
            < P @ Process | EL % BL % GL % CTRL >
       else < C @ Cell | CVS % CLS >
            < P @@ Process | EL % Meta % BL %
                                  'cv-write [ C , CV , V ] , GL % CTRL >
       fi)
  else < C @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % 'cv-write [ C , CV , V ] , GL % CTRL >]
  fi .
--> done

--
-- cv-read
-- 
--> cv-read
trans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'cv-read [ C , CV , V ] , GL % CTRL >
  =>
  if cv-exists( CV , CVS )
  then (if get-value( CV , CVS ) =/= undef
       then (if (unify (V = get-value( CV , CVS ))) =/= failure 
            then < C @ Cell | CVS % CLS >
                 < P @ Process | EL % BL %
                                 subst( unify (V = get-value( CV , CVS )) ,
                                        GL ) %
                                 CTRL >
            else (if CTRL =/= Empty
                 then < C @ Cell | CVS % CLS >
                      < P @ Process | EL % snd( head( CTRL ) ) %
                                           fst( head( CTRL ) ) % tail( CTRL ) >
                 else < C @ Cell | CVS % CLS >
                      [< P @ Process | EL % BL %
                                       'cv-read [ C , CV , V ] , GL % CTRL >]
                 fi)
            fi)
       else < C @ Cell | CVS % CLS >
            < P @@ Process | EL % Meta % BL % 'cv-read [ C , CV , V ] , GL % CTRL >
       fi)
  else < C @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % 'cv-read [ C , CV , V ] , GL % CTRL >]
  fi .
--> done

--
-- subst-cell
--
--> subst-cell
trans
  < 'system-cell @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'subst-cell [ Old , New ] , GL % CTRL >
  =>
  if (Old in EL) and cell-exists( New , CLS ) 
  then < 'system-cell @ Cell | CVS % CLS >
       < P @ Process | subst-cell( Old , New , EL ) % 
                       << nthe( 1 , subst-cell( Old , New , EL ) ) ; 1 ; 1 >> %
                       GL % CTRL >
  else < 'system-cell @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % 'subst-cell [ Old , New ] , GL % CTRL >]
  fi .
-- 9/14 change
--  then < 'system-cell @ Cell | CVS % CLS >
--       < P @ Process | subst-cell( Old , New , EL ) % BL % GL % CTRL >
--> done

--
-- cv-take
--
--> cv-take
trans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'cv-take [ C , CV , V ] , GL % CTRL >
  =>
  if cv-exists( CV , CVS )
  then (if get-value( CV , CVS ) =/= undef
       then < C @ Cell | reset-value( CV , CVS ) % CLS >
            < P @ Process | EL % BL %
                            subst( (unify (V = get-value( CV , CVS ))), GL) %
                            CTRL >
       else (if CTRL =/= Empty
            then < C @ Cell | CVS % CLS >
                 < P @ Process | EL % snd( head( CTRL ) ) %
                                      fst( head( CTRL ) ) %
                                      tail( CTRL ) >
            else < C @ Cell | CVS % CLS >
                 [< P @ Process | EL % BL %
                                   'cv-take [ C , CV , V ] , GL % CTRL >]
            fi)
       fi)
  else < C @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % 'cv-take [ C , CV , V ] , GL % CTRL >]
  fi .
--> done

--
-- cv-set
--
--> cv-set
trans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'cv-set [ C , CV , V ] , GL % CTRL >
  =>
  if cv-exists( CV , CVS )
  then < C @ Cell | write-value( CV , V , CVS ) % CLS >
       < P @ Process | EL % BL % GL % CTRL >
  else < C @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % 'cv-set [ C , CV , V ] , GL % CTRL >]
  fi .
--> done

--
-- cv-ref
--
--> cv-ref
trans
  < C @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'cv-ref [ C , CV , V ] , GL % CTRL >
  =>
  if cv-exists( CV , CVS )
  then (if get-value( CV , CVS ) =/= undef
       then (if (unify ( V = get-value( CV , CVS ))) =/= failure
            then < C @ Cell | CVS % CLS >
                 < P @ Process | EL % BL %
                                 subst( (unify ( V = get-value( CV , CVS ) )) ,
                                         GL) %
                                 CTRL >
            else (if CTRL =/= Empty
                 then < C @ Cell | CVS % CLS >
                      < P @ Process | EL % snd( head( CTRL ) ) %
                                           fst( head( CTRL ) ) % 
                                           tail( CTRL ) >
                 else < C @ Cell | CVS % CLS >
                      [< P @ Process | EL % BL % 'cv-ref [ C , CV , V ] , GL % CTRL >]
                 fi)
            fi)
       else (if CTRL =/= Empty
            then < C @ Cell | CVS % CLS >
                 < P @ Process | EL % snd( head( CTRL ) ) %
                                      fst( head( CTRL ) ) % 
                                      tail( CTRL ) >
            else < C @ Cell | CVS % CLS >
                 [< P @ Process | EL % BL % 'cv-ref [ C , CV , V ] , GL % CTRL >]
            fi)
        fi)
  else < C @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % 'cv-ref [ C , CV , V ] , GL % CTRL >]
  fi .
--> done

--
-- die
--
--> die
trans
  < 'system-cell @ Cell | CVS % CLS >
  < P @@ Process | EL % Meta % BL % 'die [ nil ] , GL % CTRL >
  =>
  if process-exists( P , CLS )
  then < 'system-cell @ Cell | CVS % process-delete( P , CLS ) >
  else < 'system-cell @ Cell | CVS % CLS >
       [< P @ Process | EL % BL % 'die [ nil ] , GL % CTRL >]
  fi .
  }
}
--> dead!!
select STATES

eof

exec
 < 'com @ Cell | << 'message ; undef >> % NoClause >
 < 'stop @ Cell | NoCVPair %
                 ('e [ nil ] : 'not [ 'find [ 'None3 ] ] := 'output [ 'resume ] ,
                       'subst_cell [ 'stop , 'proceed ])
                 ('e [ nil ] := 'name [ 'M ] , 'output [ 'waiting [ 'M ] ]) >
 < 'proceed @ Cell | NoCVPair %
                     ('e [ nil ] : 'loc [ 5 ] := 'name [ 'M ] ,
                                   'output [ 'want-enter [ 'M ] ] ,
                                   'subst-cell [ 'proceed , 'want ])
                     ('e [ nil ] : 'loc [ 8 ] := 'name [ 'M ] ,
                                   'output [ 'finished [ 'M ] ] ,
                                   'cv-take [ 'M , 'loc , 'None1 ] ,
                                   'cv-take [ 'M , 'iloc , 'None2 ] ,
                                   'die [ nil ])
                     ('e [ nil ] := 'inc [ 'loc ] , 'loc [ 'L ] , 'name [ 'M ] ,
                             'output [ 'at [ 'M , 'L ] ]) >
 < 'want @ Cell | NoCVPair %
                   ('e [ nil ] : 'find [ 'entered ] := 'output [ 'someone-there ] ,
                        'subst-cell [ 'want , 'stop ])
                   ('e [ nil ] := 'enter [ nil ] , 'subst-cell [ 'want , 'enter ])
                   ('enter [ nil ] := 'name [ 'M ] , 'output [ 'entering [ 'M ] ] ,
                                      'message [ 'entered ] ,
                                       'cv-set [ 'M , 'iloc , 1 ]) >
 < 'enter @ Cell | NoCVPair %
                   ('e [ nil ] : 'iloc [ 3 ] := 'name [ 'M ] ,
                                 'output [ 'exiting [ 'M ] ] ,
                                 'succeed [ 'cv-take [ 'com , 'message , 'None ] ] ,
                                 'inc [ 'loc ] , 'subst-cell [ 'enter , 'proceed ])
                   ('e [ nil ] := 'inc [ 'iloc ] , 'iloc [ 'LL ] , 'name [ 'M ] ,
                                  'output [ 'inside [ 'M , 'LL ] ]) > 
 < 'display @ Cell | NoCVPair % NoClause >
 < 'stdlib @ Cell | NoCVPair % 
                    ('once [ 'Goal ] :  'Goal  , ! )
                    ('succeed [ 'Goal ] : 'Goal  , !)
                    ('succedd [ 'None4 ] : True )
                    ('not [ 'Goal ] : 'once [ 'Goal ] := fail )
                    ('not [ 'None5 ] : True )
                    ('or [ 'goals [ 'X ] , 'goals [ 'Y ] ] : 'X )
                    ('or [ 'goals [ 'X ] , 'goals [ 'Y ] ] : 'Y )
                    ('repeat [ 'Goal ] : 'repeat-try [ 'Goal ] , fail)
                    ('repeat-try [ 'Goal ] : 'not [ 'Goal ] := fail)
                    ('repeat-try [ 'Goal ] : ! , 'repeat-try [ 'Goal ]) >
  < 'main @ Cell | NoCVPair % 
                   ('test [ nil ] := 'fork [ 'agent [ 'a , 1 ] ] ,
                         'fork [ 'agent [ 'b , 1 ] ])
                   ('agent [ 'M , 'Loc ] := 'new-cell [ 'M , 'loc , 'iloc ] ,
                         'push [ 'M ] , 
                         'or [ 'goals [ 'name [ 'M ] ] ,
                               'goals [  'assert [ 'name [ 'M ] ] ] ] ,
                         'cv-write [ 'M , 'loc , 'Loc ] ,
                         'push [ 'proceed ] ,
                         'output [ 'initializing [ 'M , 'Loc ] ] ,
                         'repeat [ 'e [ nil ] ])
                   ('find [ 'Mode ] := 
                         'cv-ref [ 'com , 'message , 'pair [ 'Name , 'Mode ] ],
                         'name [ 'M ] , 'not [ 'eq [ 'Name , 'M ] ])
                   ('message [ 'Mes ] := 'name [ 'M ] ,
                         'cv-write [ 'com , 'message , 'pair [ 'M , 'Mes ] ] ,
                         'output [ 'pair [ 'M , 'Mes ] ])
                   ('loc [ 'L ] := 'name [ 'M ] , 'cv-read [ 'M , 'loc , 'L ])
                   ('iloc [ 'LL ] := 'name [ 'M ] , 'cv-read [ 'M , 'iloc , 'LL ])
                   ('decr [ 'V ] : 'name [ 'M ] , 'cv-take [ 'M , 'V , 'L ] :=
                         'sub [ 'L , 1 , 'L1 ] , 'cv-set [ 'M , 'V , 'L1 ])
                   ('inc [ 'V ] : 'name [ 'M ] , 'cv-take [ 'M , 'V , 'LV ] :=
                         'add [ 'LV , 1 , 'L1 ] , 'cv-set [ 'M , 'V , 'L1 ])
                   ('output [ 'M ] := 'write [ 'M ] , nl ) >
  < 'system-cell @ Cell | << 'a ; 'newa >> << 'b ; 'newb >> %
                                     ('cell [ 'proceed ] := True)
                                     ('cell [ 'want ] := True)
                                     ('cell [ 'enter ] := True)
                                     ('cell [ 'stop ] := True)
                                     ('cell [ 'main ] := True)
                                     ('cell [ 'stdlib ] := True)
                                     ('cell [ 'system-cell ] := True)
                                     ('process [ 'main ] := True) >
  < 'main @ Process | 'main 'stdlib 'system-cell %
                      << 'main ; 1 ; 1 >> % 'test [ nil ] % Empty > .
eof
-- ----->8----->8----->8----->8----->8----->8----->8----->8----->8
