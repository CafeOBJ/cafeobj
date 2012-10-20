-- From: Hiroshi Ishikawa <h-ishika@jaist.ac.jp>
-- Date: Mon, 6 Oct 97 19:35:10 JST
-- Message-Id: <9710061035.AA00552@copper.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject: Information on Maude
-- Content-Type: text
-- Content-Length: 58579

-- 石川です．

-- Maude の件ですが，言語仕様に関する文書は現状では存在しないようです．
-- 私が使用した版は SunOS, Linux 版とも alpha 27 というものでした．

-- 詳細はインプリメンタである，Dr. Steven Eker さんに直接伺うのがよいかと思い
-- ます．私の場合は Manuel Clavel さんに手解きを受けたのですが，彼から聞いた
-- 事は，

--   built-in module は QID, MACHINE-INT のみ．BOOL は自動的に組み込まれる．
--   parameterized module は定義できない．
--   user defined module の輸入は不可．よって以下の例のように plain module
--   'fmod' と 'endfm' で等式のみの仕様を記述
--   'mod' と 'endm' で等式および遷移規則を必要とする仕様を記述
--   オペレータは prefix のみ可能
--   オペレータ属性は，以下の3通りが可能．assoc & id は現在は不可．
--      assoc, 
--      assoc and comm, 
--      assoc, comm, and id
--   オペレータは多重定義不可．

-- といったものです．
-- 以下に添付するコードは，先程お送りした gaea.mod とほぼ同等のコードです．
-- ---
-- --- 
-- ---
--> defining GAEA

module! GAEA {
  --> term and termlist ---
  imports {
    protecting (QID)
    protecting (INT)
  }

  [ Id Int < Term < NeTermList < TermList ]

  op nil : -> TermList 
  op True : -> Term 
  op ! : -> Term 
  op fail : -> Term 
  op undef : -> Term 
  op termlist : TermList TermList -> TermList { assoc }
  op termlist : NeTermList TermList -> NeTermList 
  op length : TermList -> Int 
  op pred : Id TermList -> Term 
  op belongsto : Term TermList -> Bool 

  vars TL TL' : TermList 

  vars T B : Term 

  -- make nil identity of termlist ---
  eq termlist( nil , TL ) = TL .
  eq termlist( TL , nil ) = TL .
  -- ----------------------------------
  eq length( nil ) = 0 .
  eq length( T ) = 1 .
  eq length( termlist( T , TL ) ) = 1 + length( TL ) .

  eq belongsto( ! , TL ) = true .
  eq belongsto( fail , TL ) = true .
  eq belongsto( pred( T , TL ) , nil ) = false .
  eq belongsto( pred( T , TL ) , B ) = if T == B then true else false fi .
  eq belongsto( pred( T , TL ) , termlist( B , TL' ) )
     = if T == B then true else belongsto( pred( T , TL ) , TL' ) fi .

  **> eqn and system
  [ Eqn < NeSystem < System ]
  op null : -> System 
  op && : System System -> System { assoc }
  op eqn : Term Term -> Eqn 
  op sys : System -> System 
  op eqn : TermList TermList -> System 
  op syslen : System -> Int 

  vars U V : Term 
  var UL : NeTermList 
  var S : System 
  var Sn : NeSystem 
  var Eq : Eqn 
  vars M N : Int 

  --> make null identity of list of equations ---
  eq &&( null , S ) = S .
  eq &&( S , null ) = S .
  -- -------------------------------------------

  eq eqn( termlist( T , TL ) , termlist( U , UL ) )
     = &&( eqn( T , U ) , eqn( TL , UL ) ) .


  eq syslen( Eq ) = 1 .
  eq syslen( &&( Eq , S ) ) = 1 + syslen( S ) .

  op let-be-in-term : Id Term Term -> Term 
  op let-be-in-termlist : Id Term TermList -> TermList 
  op let-be-in-eqn : Id Term Eqn -> Eqn 
  op let-be-in-system : Id Term System -> System 

  vars F X Y : Id
  eq let-be-in-termlist( X , T , nil ) = nil .

  eq let-be-in-term( X , T , Y ) = if X == Y then T else Y fi .
  eq let-be-in-term( X , T , B ) = if X == B then T else B fi .
  eq let-be-in-term( X , T , pred( F , TL ) )
     = if length( TL ) == 1 
       then pred( F , let-be-in-term( X , T , TL ) )
       else pred( F , let-be-in-termlist( X , T , TL ) )
       fi .

  eq let-be-in-termlist( X , T , termlist( U , UL ) )
     = if length( UL ) == 1
       then termlist( let-be-in-term( X , T , U ) , 
                      let-be-in-term( X , T , UL ) )
       else termlist( let-be-in-term( X , T , U ) , 
                      let-be-in-termlist( X , T , UL ) )
       fi .

  eq let-be-in-eqn( X , T , eqn( U , V ) )
     = eqn( let-be-in-term( X , T , U ) , 
            let-be-in-term( X , T , V ) ) .

  eq let-be-in-system( X , T , null ) = null .

  eq let-be-in-system( X , T , &&( eqn( U , V ) , Sn ) )
     = if syslen( Sn ) == 1
       then &&( let-be-in-eqn( X , T , eqn( U , V ) ) , 
                let-be-in-eqn( X , T , Sn ) )
       else &&( let-be-in-eqn( X , T , eqn( U , V ) ) , 
                let-be-in-system( X , T , Sn ) )
       fi .

  **> unify --------------------------------------------------------------
  op unify : System -> System 
  op failure : -> Eqn 

  --  vars Tn Un : NeTermList .
  vars Tn Un : TermList 
  vars S' S'' : System 
  vars G G' : Id
  
  eq unify( S ) = sys( sys( S ) ) .

  eq &&( S , eqn( T , T ) ) = S .
  eq &&( eqn( T , T ) , S' ) =  S' .

  eq &&( S , failure ) = failure .
  eq &&( failure , S' ) = failure .

  eq let-be-in-system( X , T , failure ) = failure .
  eq sys( eqn( T , T ) ) = null .
  eq sys( null ) = null .
  eq sys( failure ) = failure .

  --> patch for pred('name,'M) -------------------------------
  eq sys( eqn( pred('name,T),pred('name,B) ) )
     = sys( eqn( B , T ) ) .

  eq eqn( M , N ) = if M == N then null else failure fi .
  --> patch for pred('name,'M) -------------------------------

  eq sys( eqn( pred( F , Tn ) , pred( G , Un ) ) )
     = if F == G
       then if length( Tn ) == length( Un )
            then sys( eqn( Tn , Un ) )
            else failure fi
       else failure fi .

  eq sys( &&( S , eqn( pred( F , Tn ) , pred( G , Un ) ) ) ) 
     = if F == G
       then if length( Tn ) == length( Un )
            then sys( &&( S , eqn( Tn , Un ) ) )
            else failure fi
       else failure fi .

  eq sys( &&( eqn( pred( F , Tn ) , pred( G , Un ) ) , S' ) ) 
     = if F == G
       then if length( Tn ) == length( Un )
            then sys( &&( eqn( Tn , Un ) , S' ) )
            else failure fi
       else failure fi .

  --> commutative for eqn 1
  eq sys( sys( eqn( X , T ) ) )
     = if X == T
       then sys( null )
       else sys( eqn( X , T ) )
       fi .

  --> commutative for eqn 2
  eq sys( sys( eqn( T , X ) ) )
     = if X == T
       then sys( null )
       else sys( eqn( X , T ) )
       fi .

  --> commutative for eqn 1
  eq sys( sys( &&( S , eqn( X , T ) ) ) )
     = if X == T
       then sys(  S  )
       else if syslen( S ) == 1
            then sys( &&( eqn( X , T ) , 
                          sys( let-be-in-eqn( X , T , S ) ) ) )
            else sys( &&( eqn( X , T ) , 
                          sys( let-be-in-system( X , T , S ) ) ) )
            fi
       fi .

  --> commutative for eqn 2
  eq sys( sys( &&( S , eqn( T , X ) ) ) )
     = if X == T
       then sys(  S  )
       else if syslen( S ) == 1
            then sys( &&( eqn( X , T ) , 
                          sys( let-be-in-eqn( X , T , S ) ) ) )
            else sys( &&( eqn( X , T ) , 
                          sys( let-be-in-system( X , T , S ) ) ) )
            fi
       fi .

  --> commutative for eqn 1
  eq sys( sys( &&( eqn( X , T ) , S ) ) )
     = if X == T
       then sys( S )
       else if syslen( S ) == 1
            then sys( &&( eqn( X , T ) , 
                          sys( let-be-in-eqn( X , T , S ) ) ) )
            else sys( &&( eqn( X , T ) , 
                          sys( let-be-in-system( X , T , S ) ) ) )
            fi
       fi .

  --> commutative for eqn 2
  eq sys( sys( &&( eqn( T , X ) , S ) ) )
     = if X == T
       then sys( S )
       else if syslen( S ) == 1
            then sys( &&( eqn( X , T ) , 
                          sys( let-be-in-eqn( X , T , S ) ) ) )
            else sys( &&( eqn( X , T ) , 
                          sys( let-be-in-system( X , T , S ) ) ) )
            fi
       fi .

  --> commutative for eqn 1
  eq sys( &&( S , sys( eqn( X , T ) ) ) )
     = if X == T
       then sys( S )
       else if syslen( S ) == 1
            then sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ) )
            else sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ) )
            fi
       fi .

  --> commutative for eqn 2
  eq sys( &&( S , sys( eqn( T , X ) ) ) )
     = if X == T
       then sys( S )
       else if syslen( S ) == 1
            then sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ) )
            else sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ) )
            fi
       fi .

  --> commutative for eqn 1
  eq sys( &&( S , sys( &&( S' , eqn( X , T ) ) ) ) )
     = if X == T
       then sys( &&( S , S' ) )
       else if syslen( S ) == 1
            then if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            else if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            fi

       fi .

  --> commutative for eqn 2
  eq sys( &&( S , sys( &&( S' , eqn( T , X ) ) ) ) )
     = if X == T
       then sys( &&( S , S' ) )
       else if syslen( S ) == 1
            then if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            else if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            fi
       fi .

  --> commutative for eqn 1
  eq sys( &&( S , sys( &&( eqn( X , T ) , S' ) ) ) )
     = if X == T
       then sys( &&( S , S' ) )
       else if syslen( S ) == 1
            then if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            else if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            fi

       fi .

  --> commutative for eqn 2
  eq sys( &&( S , sys( &&( eqn( T , X ) , S' ) ) ) )
     = if X == T
       then sys( &&( S , S' ) )
       else if syslen( S ) == 1
            then if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-eqn( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            else if syslen( S' ) == 1
                 then sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-eqn( X , T , S' ) ) ) )
                 else sys( &&( eqn( X , T ) , let-be-in-system( X , T , S ) ,
                               sys( let-be-in-system( X , T , S' ) ) ) )
                 fi
            fi
       fi .
  -- end unify ----------------------------------------------------------

  **> subst-term ---------------------------------------------------------
  op subst : System TermList -> TermList 
  op substmain : Eqn TermList -> TermList

  eq subst( null , TL ) = TL .
  eq subst( eqn( X , T ) , TL ) = substmain( eqn( X , T ) , TL ) .
  eq subst( sys( eqn( X , T ) ) , TL ) = substmain( eqn( X , T ) , TL ) .
  eq subst( sys( &&( eqn( X , T ) , S ) ) , TL )
     = subst( S , substmain( eqn( X , T ) , TL ) ) .

  eq substmain( eqn( X , T ) , nil ) = nil .
  eq substmain( eqn( X , T ) , pred( F ,  TL ) )
     = pred( F , substmain( eqn( X , T ) , TL ) ) .
  eq substmain( eqn( X , T ) , termlist( pred( F ,  TL ) , TL' ) )
     = termlist( pred( F , substmain( eqn( X , T ) , TL ) ) ,
                 substmain( eqn( X , T ) , TL' ) ) .

  eq substmain( eqn( X , T ) , U )
     = if X == U then T else U fi .
  eq substmain( eqn( X , T ) , termlist( U , TL ) )
     = if X == U
       then termlist( T , substmain( eqn( X , T ) , TL ) )
       else termlist( U , substmain( eqn( X , T ) , TL ) )
       fi .

  --> clause and clauselist -------------------------------------------------
  [ Clause < ClauseList ]

  op ClError : -> Clause 
  op NoClause : -> ClauseList 
  op clause : ClauseList ClauseList -> ClauseList {assoc}
  op cldef : Term TermList TermList -> Clause 
  -- _:_ -> cldef( H , nil , B ) .
  -- _:=_ -> cldef( H , nil , termlist(! , B )) .
  -- _:_:=_ -> cldef( H , Cond , termlist(!,B )) .

  op head-part : Clause -> Term 
  op body-part : Clause -> TermList 
 
  op nthcl : Int ClauseList -> Clause 

  op cell-exists : Term ClauseList -> Bool 
  op process-exists : Term ClauseList -> Bool 
  op process-delete : Term ClauseList -> ClauseList 

  var Cl : Clause 
  var CLS : ClauseList 
  --  vars M N : Int .
  var T' : Term 

  eq clause( NoClause , CLS ) = CLS .
  eq clause( CLS , NoClause ) = CLS .

  eq head-part( cldef( T , TL , TL' ) ) = T .

  eq body-part( cldef( T , nil , TL ) ) = TL .
  eq body-part( cldef( T , TL , TL' ) ) = termlist( TL , TL' ) .


  cq nthcl( M , CLS ) = ClError if M < 1 .
  eq nthcl( M , NoClause ) = ClError .
  eq nthcl( M , Cl ) = if M == 1 then Cl else ClError fi .
  eq nthcl( M , clause( Cl , CLS ) )
     = if M == 1 then Cl else nthcl( M - 1 , CLS ) fi .

  eq cell-exists( T , NoClause ) = false .
  eq cell-exists( T , cldef( pred( X , T' ) , TL , TL' ) )
     = if X == 'cell
       then if T == T'
            then true else false fi
       else false
       fi .
  eq cell-exists( T , clause( cldef( pred( X , T' ) , TL , TL' ) , CLS ) )
     = if X == 'cell
       then if T == T'
            then true
            else cell-exists( T , CLS )
            fi
       else cell-exists( T , CLS )
       fi .

  eq process-exists( T , NoClause ) = false .
  eq process-exists( T , cldef( pred( X , T' ) , TL , TL' ) )
     = if X == 'process
       then if T == T'
            then true else false fi
       else false
       fi .
  eq process-exists( T , clause( cldef( pred( X , T' ) , TL , TL' ) , CLS ) )
     = if X == 'process
       then if T == T'
            then true else process-exists( T , CLS )
            fi
       else process-exists( T , CLS )
       fi .

  eq process-delete( T , NoClause ) = NoClause .
  eq process-delete( T , cldef( pred( X , T' ) , nil , ! ) )
     = if X == 'process
       then if T == T' 
            then NoClause 
            else cldef( pred( X , T' ) , nil , ! ) 
            fi
       else cldef( pred( X , T' ) , nil , ! )
       fi .
  eq process-delete( T , clause( cldef( pred( X , T' ) , nil , ! ) , CLS ) )
     = if X == 'process
       then if T == T'
            then CLS
            else clause( cldef( pred( X , T' ) , nil , ! ) ,
                         process-delete( T , CLS ) )
            fi
       else clause( cldef( pred( X , T' ) , nil , ! ) ,
                    process-delete( T , CLS ) )
       fi .
  --> location -------------------------------------------------------------
  [  Loc ]
  
  op loc : Id Int Int -> Loc 
  op NoLoc : -> Loc 
  op Meta : -> Loc 

  --> cell variable pairs ----------------------------------------------------
  [ CVPair < CVPairList ]

  op NoCVPair : -> CVPairList 
  op cvpair : Id Term -> CVPair 
  op cvs : CVPairList CVPairList -> CVPairList { assoc }

  op cv-exists : Term CVPairList -> Bool 
  op write-value : Term Term CVPairList -> CVPairList 
  op get-value : Term CVPairList -> Term 
  op reset-value : Term CVPairList -> CVPairList 
  op create-pid : Term CVPairList -> Id 
  op create-cvpairs : TermList -> CVPairList 

  vars CVS : CVPairList 

  eq cvs( NoCVPair , CVS ) = CVS .
  eq cvs( CVS , NoCVPair ) = CVS .

  eq cv-exists( T , NoCVPair ) = false .
  eq cv-exists( T , cvpair( T' , V ) )
     = if T == T' then true else false fi .
  eq cv-exists( T , cvs( cvpair( T' , V ) , CVS ) )
     = if T == T' 
       then true 
       else cv-exists( T , CVS )
       fi .

  eq get-value( T , cvpair( T , V ) ) = V .
  eq get-value( T , cvs( cvpair( T' , V ) , CVS ) )
     = if T == T'
       then V
       else get-value( T , CVS )
       fi .

  eq write-value( T , V , cvpair( T , U ) ) = cvpair( T , V ) .
  eq write-value( T , V , cvs( cvpair( T' , U ) , CVS ) )
     = if T == T'
       then cvs( cvpair( T , V ) , CVS )
       else cvs( cvpair( T' , U ) , write-value( T , V , CVS ) )
       fi .

  eq reset-value( T , cvpair( T , V ) ) = cvpair( T , undef ) .
  eq reset-value( T , cvs( cvpair( T' , V ) , CVS ) )
     = if T == T'
       then cvs( cvpair( T , undef ) , CVS )
       else cvs( cvpair( T' , V ) , reset-value( T , CVS ) )
       fi .

  eq create-pid( pred( 'agent , termlist( T , N ) ) , cvpair( T , X ) )
     = X .
  eq create-pid( pred( 'agent , termlist( T , N ) ) , 
                 cvs( cvpair( T' , X ) , CVS ) )
     = if T == T'
       then X
       else create-pid( pred( 'agent , termlist( T , N ) ) , CVS )
       fi .

  eq create-cvpairs( nil ) = NoCVPair .
  eq create-cvpairs( T ) = cvpair( T , undef ) .
  eq create-cvpairs( termlist( T , TL ) )
     = cvs( cvpair( T , undef ) , create-cvpairs( TL ) ) .

  --> control and controllist --------------------------------------------
  [ Control < ControlList ]

  op ctrl : TermList Loc -> Control 
  op ctrllist : ControlList ControlList -> ControlList { assoc }
  op Empty : -> ControlList 

  op fst : Control -> TermList 
  op snd : Control -> Loc 
  op head : ControlList -> Control 
  op tail : ControlList -> ControlList 
  op assert-inc : Id ControlList -> ControlList 
  op push-cell : Id ControlList -> ControlList 

  var L : Loc 
  var Ctrl : Control 
  var Ctrls : ControlList 

  eq ctrllist( Empty , Ctrls ) = Ctrls .
  eq ctrllist( Ctrls , Empty ) = Ctrls .

  eq fst( ctrl( TL , L ) ) = TL .
  eq snd( ctrl( TL , L ) ) = L .

  eq head( Ctrl ) = Ctrl .
  eq head( ctrllist( Ctrl , Ctrls ) ) = Ctrl .
  eq tail( Ctrl ) = Empty .
  eq tail( ctrllist( Ctrl , Ctrls ) ) = Ctrls .

  eq assert-inc( X , Empty ) = Empty .
  eq assert-inc( X , ctrl( TL , loc( Y , M , N ) ) )
     = if X == Y
       then ctrl( TL , loc( Y , M , N + 1 ) )
       else ctrl( TL , loc( Y , M , N ) )
       fi .
  eq assert-inc( X , ctrllist( ctrl( TL , loc( Y , M , N ) ) , Ctrls ) )
     = if X == Y
       then ctrllist( ctrl( TL , loc( Y , M , N + 1 ) ) ,
                      assert-inc( X , Ctrls ) )
       else ctrllist( ctrl( TL , loc( Y , M , N ) ) ,
                      assert-inc( X , Ctrls ) )
       fi .

  eq push-cell( G , Empty ) = Empty .
  eq push-cell( G , ctrl( T , loc( G' , M , N ) ) )
     = if G == G'
       then ctrl( T , loc( G' , M + 1 , N ) )
       else ctrl( T , loc( G' , M , N ) )
       fi .
  eq push-cell( G , ctrl( TL , loc( G' , M , N ) ) )
     = if G == G'
       then ctrl( TL , loc( G' , M + 1 , N ) )
       else ctrl( TL , loc( G' , M , N ) )
       fi .
  eq push-cell( G , ctrllist( ctrl( T , loc( G' , M , N ) ) , Ctrls ) )
     = if G == G'
       then ctrllist( ctrl( T , loc( G' , M + 1 , N ) ) , push-cell( G , Ctrls ) )
       else ctrllist( ctrl( T , loc( G' , M , N ) ) , push-cell( G , Ctrls ) )
       fi .
  eq push-cell( G , ctrllist( ctrl( TL , loc( G' , M , N ) ) , Ctrls ) )
     = if G == G'
       then ctrllist( ctrl( TL , loc( G' , M + 1 , N ) ) , push-cell( G , Ctrls ) )
       else ctrllist( ctrl( TL , loc( G' , M , N ) ) , push-cell( G , Ctrls ) )
       fi .

  --> environment ----------------------------------------------------
  [ Id < Env < EnvList ]

  op NoEnv : -> Env 
  op env : EnvList EnvList -> EnvList { assoc } 
  op EnvError : -> Env 
  op in : Env EnvList -> Bool 
  op nthe : Int EnvList -> Env 
  op subst-cell : Id Id EnvList -> EnvList 

  vars E E' : Id 
  var EL : EnvList 
  vars Old New : Id

  eq env( NoEnv , EL ) = EL .
  eq env( EL , NoEnv ) = EL .

  eq in( E , NoEnv ) = false .
  eq in( E , E' ) = E == E' .
  eq in( E , env( E' , EL ) )
     = if E == E' then true else in( E , EL ) fi .

  cq nthe( M , EL ) = EnvError if M < 1 .
  eq nthe( M , E ) = if M == 1 then E else EnvError fi .
  eq nthe( M , env( E , EL ) )
     = if M == 1 then E else nthe( M - 1 , EL ) fi .

  eq subst-cell( Old , New , NoEnv ) = NoEnv .
  eq subst-cell( Old , New , Old ) = New .
  eq subst-cell( Old , New , env( E , EL ) )
     = if Old == E
       then env( New , EL )
       else env( E , subst-cell( Old , New , EL ) )
       fi .

  --> state --------------------------------------------
  [ Object < State, 
    Message State ]

  op cell : Id CVPairList ClauseList -> Object 
  op process : Id EnvList Loc TermList ControlList -> Object 
  op eprocess : Id EnvList Loc TermList ControlList -> Object 
  op cprocess : Id EnvList Loc Loc TermList ControlList -> Object 
  op error : Object -> Object 

  op state : State State -> State { assoc comm }

  vars P P' CV : Id 
  var CVS' : CVPairList 
  var CLS' : ClauseList 
  var BL : Loc 
  var W : Term 
  vars GL WL : TermList 
  vars A1 A2 : Term 

  -- cut
  trans
  cprocess( P , EL , Meta , L , ! , Ctrls )
  =>
  if Ctrls =/= Empty
  then process( P , EL , L , nil , tail( Ctrls ) )
  else process( P , EL , L , nil , Ctrls )
  fi .

  trans
  cprocess( P , EL , Meta , L , termlist( ! , TL ) , Ctrls )
  =>
  if Ctrls =/= Empty
  then process( P , EL , L , TL , tail( Ctrls ) )
  else process( P , EL , L , TL , Ctrls ) 
  fi .

  -- fail
  trans
  cprocess( P , EL , Meta , L , fail , Ctrls )
  => 
  if Ctrls =/= Empty
  then process( P , EL , snd(head(Ctrls)) , fst(head(Ctrls)) ,tail( Ctrls ) )
  else eprocess( P , EL , L , fail , Ctrls ) 
  fi .

  trans
  cprocess( P , EL , Meta , L , termlist( fail , TL ) , Ctrls )
  => 
  if Ctrls =/= Empty
  then process( P , EL , snd(head(Ctrls)) , fst(head(Ctrls)), tail(Ctrls) )
  else eprocess( P , EL , L , termlist(fail,TL),Ctrls ) 
  fi .

  -- write
  trans
  state( cell('display , CVS , CLS ) ,
         cprocess( P , EL , Meta , L , pred( 'wreite,T), Ctrls ) )
  =>
  state( process( P , EL , L , nil , Ctrls ) ,
         cell( 'display , CVS , clause( cldef( 'write , nil , T ) ,CLS ) ) ) .

  trans
  state( cprocess( P , EL , Meta , L , termlist( pred('write,T),TL),Ctrls ) ,
         cell( 'display , CVS , CLS ) )
  =>
  state( process( P , EL , L , TL , Ctrls ) ,
         cell( 'display , CVS , clause( cldef( 'write , nil , T ) ,CLS ) ) ) .

  -- nl
  trans
  cprocess( P , EL , Meta , L , pred('nl,nil),Ctrls )
  =>
  process( P , EL , L , nil , Ctrls ) .

  trans
  cprocess( P , EL , Meta , L , termlist(pred('nl,nil),TL),Ctrls )
  =>
  process( P , EL , L , TL , Ctrls ) .

  -- add
  trans
  cprocess( P , EL , Meta , L ,
            termlist( pred( 'add , termlist( M , N , T ) ) , TL ) , Ctrls )
  =>
  process( P , EL , L , subst( sys(eqn(T,M + N)) , TL) , Ctrls ) .

  -- eq
  trans
  cprocess( P , EL , Meta , L , 
            termlist( pred( 'eq , termlist( TL , UL ) ) , WL) , Ctrls )
  =>
  if unify( eqn( TL , UL ) ) =/= failure
  then process( P , EL , L , subst(unify(eqn(TL,UL)),WL) , Ctrls )
  else if Ctrls =/= Empty
       then process( P , EL , snd(head(Ctrls)) , fst(head(Ctrls)), tail( Ctrls ) )
       else eprocess(P,EL,L,termlist(pred('eq,termlist(TL,UL)),WL),Ctrls) 
       fi
  fi .


  -- classification rule
  trans
  process( P , EL , L , T , Ctrls )
  =>
  if belongsto( T , termlist( ! , fail , 'write, 'nl , 'add , 'eq ) )
  then cprocess( P , EL , Meta , L , T , Ctrls )
  else 
    (if belongsto( T , termlist( 'fork , 'new-cell , 'push , 'assert ,
                                'cv-write , 'cv-take , 'cv-set ,
                                'cv-ref , 'subst-cell , 'cv-read , 'die ) )
    then cprocess( P , EL , Meta , L , T , Ctrls )
    else cprocess( P , EL , L , NoLoc , T , Ctrls )
    fi)
  fi .

  trans
  process( P , EL , L , termlist(T,TL),Ctrls )
  =>
  if belongsto( T , termlist( ! , fail , 'write, 'nl , 'add , 'eq ) )
  then cprocess( P , EL , Meta , L , termlist(T,TL),Ctrls )
  else
    (if belongsto( T , termlist( 'fork , 'new-cell , 'push , 'assert ,
                              'cv-write , 'cv-take , 'cv-set ,
                              'cv-ref , 'subst-cell , 'cv-read , 'die ) )
    then cprocess( P , EL , Meta , L , termlist(T,TL),Ctrls )
    else cprocess( P , EL , L , NoLoc , termlist(T,TL),Ctrls )
    fi)
  fi .

  -- main rule no.1
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , loc( E , M , N ) , BL , T , Ctrls ) )
  =>
  if BL == NoLoc
  then
    (if in( E , EL )
    then
      (if nthcl( N , CLS ) =/= ClError
      then
        (if unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) =/= failure
        then state( cell( E , CVS , CLS ) ,
             process( P , EL , loc( nthe( 1 , EL ) , 1 , 1 ) ,
                      subst( unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) ,
                                body-part( nthcl( N , CLS ) ) ) ,
                      ctrllist( ctrl( T , loc( E , M , N + 1 ) ) ,
                                Ctrls ) ) )
        else state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( E , M , N + 1 ) , BL , T , Ctrls ) )
        fi)
      else
        (if nthe( M + 1 , EL ) =/= EnvError
        then state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( nthe( M + 1 , EL ) , M + 1 , 1 ) ,
                              BL , T , Ctrls ) )
        else
          (if Ctrls =/= Empty
          then state( cell( E , CVS , CLS ) ,
                      process( P , EL , snd(head(Ctrls)) , 
                               fst(head(Ctrls)),tail( Ctrls ) ) )
          else state( cell( E , CVS , CLS ) ,
                      cprocess( P , EL , loc( E , M , N ) , BL , T , Ctrls ) )
          fi)
        fi)
      fi)
    else
      (if Ctrls =/= Empty
      then state( cell( E , CVS , CLS ) ,
                  process( P , EL , snd(head(Ctrls)) , 
                           fst(head(Ctrls)),tail( Ctrls ) ))
      else state( cell( E , CVS , CLS ) ,
                  eprocess( P , EL , BL , T , Ctrls ) )
      fi)
    fi)
  else
    (if in( E , EL )
    then
      (if nthcl( N , CLS ) =/= ClError
      then 
        (if unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) =/= failure
        then state( cell( E , CVS , CLS ) ,
             process( P , EL , loc( nthe( 1 , EL ) , 1 , 1 ) ,
                      subst( unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) ,
                                body-part( nthcl( N , CLS ) ) ) ,
                      ctrllist( ctrl( T , loc( E , M , N + 1 ) ) ,
                                Ctrls ) ) )
        else state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( E , M , N + 1 ) , BL , T , Ctrls ) )
        fi)
      else
        (if nthe( M + 1 , EL ) =/= EnvError
        then state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( nthe( M + 1 , EL ) , M + 1 , 1 ) ,
                             BL , T , Ctrls ) )
        else state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , Meta , BL , T , Ctrls ) )
        fi)
      fi)
    else
      (if Ctrls =/= Empty
      then state( cell( E , CVS , CLS ) ,
                  process( P , EL , snd( head( Ctrls ) ) , 
                          fst( head( Ctrls ) ),tail( Ctrls ) ) )
      else state( cell( E , CVS , CLS ) ,
                  eprocess( P , EL , BL , T , Ctrls ) ) 
      fi)
    fi)
  fi .

  -- main rule no.2
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , loc( E , M , N ) , BL , termlist( T , TL ), Ctrls ) )
  =>
  if BL == NoLoc
  then
    (if in( E , EL )
    then
      (if nthcl( N , CLS ) =/= ClError
      then
        (if unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) =/= failure
        then state( cell( E , CVS , CLS ) ,
             process( P , EL , loc( nthe( 1 , EL ) , 1 , 1 ) ,
                      subst( unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) ,
                                termlist( body-part( nthcl( N , CLS ) ) , TL ) ) ,
                      ctrllist( ctrl( termlist( T , TL ) , loc( E , M , N + 1 ) ) ,
                                Ctrls ) ) )
        else state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( E , M , N + 1 ) , BL , 
                              termlist( T , TL ),Ctrls ) )
        fi)
      else
        (if nthe( M + 1 , EL ) =/= EnvError
        then state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( nthe( M + 1 , EL ) , M + 1 , 1 ) ,
                              BL , termlist( T , TL ) , Ctrls ) )
        else
          (if Ctrls =/= Empty
          then state( cell( E , CVS , CLS ) ,
                      process( P , EL , snd( head( Ctrls ) ) , 
                               fst( head( Ctrls ) ) ,tail( Ctrls ) ) )
          else state( cell( E , CVS , CLS ) ,
                      eprocess( P , EL , BL , termlist( T , TL ) ,Ctrls ) ) 
          fi)
        fi)
      fi)
    else
      (if Ctrls =/= Empty
      then state( cell( E , CVS , CLS ) ,
                  process( P , EL , snd( head( Ctrls ) ) , 
                           fst( head( Ctrls ) ) ,tail( Ctrls ) ) )
      else state( cell( E , CVS , CLS ) ,
                  eprocess( P , EL , BL , termlist( T , TL ) , Ctrls ) ) 
      fi)
    fi)
  else
    (if in( E , EL )
    then
      (if nthcl( N , CLS ) =/= ClError
      then 
        (if unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) =/= failure
        then state( cell( E , CVS , CLS ) ,
             process( P , EL , loc( nthe( 1 , EL ) , 1 , 1 ) ,
                      subst( unify( eqn( head-part( nthcl( N , CLS ) ) , T ) ) ,
                                termlist( body-part( nthcl( N , CLS ) ) , TL ) ),
                      ctrllist( ctrl( termlist( T , TL ) , loc( E , M , N + 1 ) ) ,
                                Ctrls ) ) )
        else state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( E , M , N + 1 ) , BL , 
                              termlist( T , TL ) ,Ctrls ) )
        fi)
      else
        (if nthe( M + 1 , EL ) =/= EnvError
        then state( cell( E , CVS , CLS ) ,
                    cprocess( P , EL , loc( nthe( M + 1 , EL ) , M + 1 , 1 ) ,
                             BL , termlist( T , TL ) , Ctrls ) )
        else state( cell( E , CVS , CLS ) ,
                    eprocess( P , EL , BL , termlist( T , TL ) , Ctrls ))
        fi)
      fi)
    else
      (if Ctrls =/= Empty
      then state( cell( E , CVS , CLS ) ,
                  process( P , EL , snd( head( Ctrls ) ) , 
                           fst( head( Ctrls ) ) , tail( Ctrls ) ) )
      else state( cell( E , CVS , CLS ) ,
                  eprocess( P , EL , BL , termlist( T , TL ) , Ctrls ) )
      fi)
    fi)
  fi .

  --> extra features ------------------------------------------------------
  -- fork
  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , pred( 'fork , T ) , Ctrls ) )
  =>
  state( cell( 'system-cell , CVS ,
               clause( cldef( pred( 'process , create-pid( T , CVS ) ) ,
                                  nil , ! ) , CLS ) ) ,
         process( create-pid( T , CVS ) , EL , 
                  loc( nthe( 1 , EL ) , 1 , 1 ) , T , Empty ) ,
         process( P , EL , BL , nil , Ctrls ) ) .

  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , pred( 'fork , TL ) , Ctrls ) )
  =>
  state( cell( 'system-cell , CVS ,
               clause( cldef( pred( 'process , create-pid( TL , CVS ) ) ,
                                  nil , ! ) , CLS ) ) ,
         process( create-pid( TL , CVS ) , EL , 
                  loc( nthe( 1 , EL ) , 1 , 1 ) , TL , Empty ) ,
         process( P , EL , BL , nil , Ctrls ) ) .

  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   termlist( pred( 'fork , TL ) , GL ) , Ctrls ) )
  =>
  state( cell( 'system-cell , CVS ,
               clause( cldef( pred( 'process , create-pid( TL , CVS ) ) ,
                                  nil , ! ) , CLS ) ) ,
         process( create-pid( TL , CVS ) , EL , 
                  loc( nthe( 1 , EL ) , 1 , 1 ) , TL , Empty ) ,
         process( P , EL , BL , GL , Ctrls ) ) .

  -- new-cell
  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   termlist(pred('new-cell,termlist(T,A1,A2)),GL),Ctrls ))
  =>
  if cell-exists( T , CLS ) == false
  then state( cell( 'system-cell , CVS , 
                    clause( cldef( pred( 'cell , T ) , nil , ! ) , CLS ) ) ,
              cell( T , create-cvpairs( termlist(A1,A2) ) , NoClause ) ,
              process( P , EL , BL , GL , Ctrls ) )
  else state( cell( 'system-cell , CVS , CLS ) ,
       eprocess( P , EL , BL , 
             termlist(pred('new-cell,termlist(T,A1,A2) ),GL),Ctrls )) 
  fi .

-- for test ------------------
  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   pred( 'new-cell , termlist(T,A1,A2) ),Ctrls ))
  =>
  state( cell( 'system-cell , CVS , 
               clause( cldef( pred( 'cell , T ) , nil , ! ) , CLS ) ) ,
         cell( T , create-cvpairs( termlist(A1,A2) ) , NoClause ) ,
         process( P , EL , BL , nil , Ctrls ) ) .

-- for test ------------------

-- ---  rl
-- ---  state( cell( 'system-cell , CVS , CLS ) ,
-- ---         cprocess( P , EL , Meta , BL , Ctrls ) ,
-- ---         deduce( P , termlist( pred( 'new-cell , termlist( T , TL ) ) , GL ) ) )
-- ---  =>
-- ---  if cell-exists( T , CLS ) == false
-- ---  then state( cell( 'system-cell , CVS , 
-- ---                    clause( cldef( pred( 'cell , T ) , nil , termlist( ! , nil ) ) , 
-- ---                            CLS ) ) ,
-- ---              cell( T , create-cvpairs( TL ) , NoClause ) ,
-- ---              process( P , EL , BL , Ctrls ) ,
-- ---              deduce( P , GL ) )
-- ---  else state( cell( 'system-cell , CVS , CLS ) ,
-- ---       cprocess( P , EL , Meta , BL , Ctrls ) ,
-- ---       error(deduce( P , termlist( pred( 'new-cell , termlist( T , TL ) ) , GL ) ) ))
-- ---  fi .

  -- push
  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , termlist(pred('push,T),GL),Ctrls ) )
  =>
  if cell-exists( T , CLS )
  then state( cell( 'system-cell , CVS , CLS ) ,
              process( P , env( T , EL ) , loc( T , 1 , 1 ) , GL ,
                       push-cell( T , Ctrls ) ) )
  else state( cell( 'system-cell , CVS , CLS ) ,
              eprocess( P , EL , BL , 
                        termlist( pred( 'push , T ) , GL ),Ctrls ) )
  fi .

  -- assert
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , env( E , EL ) , Meta , BL ,
                   termlist( pred( 'assert , T ) , GL ) ,Ctrls ) )
  =>
  state( cell( E , CVS , clause(cldef(T,nil,!) , CLS  ) ) ,
         process( P , env( E , EL ) , BL , GL , assert-inc( E , Ctrls ) ) ) .

  -- cv-write
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , pred('cv-write,termlist(E,CV,V)),Ctrls ))
  =>
  if cv-exists( CV , CVS )
  then (if get-value( CV , CVS ) == undef
       then state( cell( E , write-value( CV , V , CVS ) , CLS ) ,
                   process( P , EL , BL , nil ,Ctrls ) )
       else state( cell( E , CVS , CLS ) ,
            cprocess(P,EL,Meta,BL,pred('cv-write,termlist(E,CV,V)),Ctrls))
       fi)
  else state(cell( E , CVS , CLS ) ,
             eprocess(P,EL,BL,pred('cv-write,termlist(E,CV,V)),Ctrls))
  fi .

  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   termlist(pred('cv-write,termlist(E,CV,V)),GL),Ctrls ) )
  =>
  if cv-exists( CV , CVS )
  then (if get-value( CV , CVS ) == undef
       then state( cell( E , write-value( CV , V , CVS ) , CLS ) ,
                   process( P , EL , BL , GL , Ctrls ) )
       else state( cell( E , CVS , CLS ) ,
            process( P , EL , BL , 
                  termlist(pred('cv-write,termlist(E,CV,V)),GL ),Ctrls ) )
       fi)
  else state( cell( E , CVS , CLS ) ,
              eprocess( P , EL , BL ,
                   termlist(pred('cv-write,termlist(E,CV,V)),GL),Ctrls ))
  fi .

  -- cv-read
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   termlist(pred('cv-read,termlist(E,CV,V)),GL),Ctrls ) )
  =>
  if cv-exists( CV , CVS )
  then
    (if get-value( CV , CVS ) =/= undef
    then
      (if unify( eqn( V , get-value( CV , CVS ) ) ) =/= failure
      then state( cell( E , CVS , CLS ) ,
                  process( P , EL , BL ,
                           subst(unify( eqn(V,get-value(CV,CVS))),GL),Ctrls ))
      else
        (if Ctrls =/= Empty
        then state( cell( E , CVS , CLS ) ,
                    process( P , EL , snd(head(Ctrls)) ,
                             fst(head(Ctrls)),tail(Ctrls) ))
        else state( cell( E , CVS , CLS ) ,
                    eprocess( P , EL ,BL ,
                                   termlist(pred('cv-read,termlist(E,CV,V)),GL),
                                   Ctrls ) )
        fi)
      fi)
    else state( cell( E , CVS , CLS ) ,
                eprocess( P , EL , BL , 
                               termlist( pred('cv-read,termlist(E,CV,V)),GL),
                               Ctrls ) )
    fi)
  else state( cell( E , CVS , CLS ) ,
              eprocess( P , EL , BL , 
                             termlist(pred('cv-read,termlist(E,CV,V)),GL),Ctrls ))
  fi .

  -- subst-cell
  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   termlist(pred('subst-cell,termlist(New,Old)),GL),Ctrls ) )
  =>
  if in( Old , EL )
  then (if cell-exists( New , CLS )
       then state( cell( 'system-cell , CVS , CLS ) ,
                   process( P , subst-cell( Old , New , EL ) ,
                                loc( nthe( 1 , subst-cell( Old , New , EL ) ) ,
                                     1 , 1 ) , GL , Ctrls ) )
       else state( cell( 'system-cell , CVS , CLS ) ,
                   eprocess( P , EL , BL , 
                             termlist( pred( 'subst-cell , 
                                              termlist( New , Old ) ) , GL ),
                             Ctrls ))
       fi)
  else state( cell( 'system-cell , CVS , CLS ) ,
              eprocess( P , EL , BL ,
                             termlist(pred('subst-cell,termlist(New,Old)),GL),
                             Ctrls))
  fi .

  -- cv-take
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   termlist( pred( 'cv-take , termlist( E , CV , V ) ) , GL ),
                   Ctrls ) )
  =>
  if cv-exists( CV , CVS )
  then
    (if get-value( CV , CVS ) =/= undef
    then state( cell( E , reset-value( CV , CVS ) , CLS ) ,
                process( P , EL , BL , 
                         subst( unify( eqn(V,get-value(CV,CVS)) ) , GL ),
                         Ctrls ))
    else
      (if Ctrls =/= Empty
      then state( cell( E , CVS , CLS ) ,
                  process( P , EL , snd( head( Ctrls ) ) , 
                           fst( head( Ctrls ) ) ,tail( Ctrls ) ) )
      else state( cell( E , CVS , CLS ) ,
                  eprocess( P , EL ,BL , 
                                 termlist( pred( 'cv-take , 
                                           termlist( E , CV , V ) ) , GL ), Ctrls ))
      fi)
    fi)
  else state( cell( E , CVS , CLS ) ,
              eprocess( P , EL , BL , 
                             termlist( pred( 'cv-take , 
                                       termlist( E , CV , V ) ) , GL),Ctrls ))
  fi .

  -- cv-set
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL ,
                   termlist(pred('cv-set,termlist(E,CV,V)),GL) , Ctrls ) )
  =>
  if cv-exists( CV , CVS )
  then state( cell( E , write-value( CV , V , CVS ) , CLS ) ,
              process( P , EL , BL , GL , Ctrls ) )
  else state( cell( E , CVS , CLS ) ,
              eprocess( P , EL , BL , 
                             termlist(pred('cv-set,termlist(E,CV,V)),GL),Ctrls))
  fi .

  -- cv-ref
  trans
  state( cell( E , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL ,
                   termlist( pred('cv-ref,termlist(E,CV,V)),GL ) , Ctrls ) )
  =>
  if cv-exists( CV , CVS )
  then
    (if get-value( CV , CVS ) =/= undef
    then
      (if unify( eqn( V , get-value( CV , CVS ) ) ) =/= failure
      then state( cell( E , CVS , CLS ) ,
           process( P , EL , BL ,
                    subst(unify(eqn(V,get-value(CV,CVS))),GL), Ctrls ))
      else
        (if Ctrls =/= Empty
        then state( cell( E , CVS , CLS ) ,
                    process( P , EL , snd( head( Ctrls ) ) , 
                             fst( head( Ctrls ) ) ,tail( Ctrls ) ))
        else state( cell( E , CVS , CLS ) ,
                    eprocess( P , EL , BL , 
                                   termlist( pred( 'cv-ref , 
                                     termlist( E , CV , V ) ) , GL ) ,Ctrls ) )
        fi)
      fi)
    else
      (if Ctrls =/= Empty
      then state( cell( E , CVS , CLS ) ,
                  process( P , EL , snd( head( Ctrls ) ) ,
                           fst( head( Ctrls ) ) , tail( Ctrls ) ) )
      else state( cell( E , CVS , CLS ) ,
                  eprocess( P , EL , BL , 
                                termlist( pred( 'cv-ref , 
                                         termlist( E , CV , V ) ) , GL ) ,Ctrls ) )
      fi)
    fi)
  else state( cell( E , CVS , CLS ) ,
              eprocess( P , EL ,BL ,
                             termlist( pred( 'cv-ref , 
                                      termlist( E , CV , V ) ) , GL ), Ctrls ) )
  fi .

  -- die
  trans
  state( cell( 'system-cell , CVS , CLS ) ,
         cprocess( P , EL , Meta , BL , 
                   termlist( pred( 'die , nil ) , GL ) ,Ctrls ) )
  =>
  if process-exists( P , CLS )
  then cell( 'system-cell , CVS , process-delete( P , CLS ) )
  else state( cell( 'system-cell , CVS , CLS ) ,
              eprocess( P , EL , BL , 
                             termlist( pred( 'die , nil ) , GL ) ,Ctrls ) )
  fi .

}


-- reduce examples -----

-- cell com ---------------------------------------------
-- red cell( 'com , cvpair( 'message , undef ) , NoClause )  .
-- cell proceed ---------------------------------------------
-- red cell( 'proceed , NoCVPair , 
--           clause(cldef( pred( 'e , nil ) , 
--                         pred( 'loc , 5 ) ,
--                         termlist( ! , pred( 'name , 'M ) ,
--                                   pred( 'output , pred( 'want-enter , 'M ) ) ,
--                                   pred( 'subst-cell , termlist('want ,'proceed)))),
--                  cldef( pred( 'e , nil ) ,
--                         pred( 'loc , 8 ) ,
--                         termlist( ! , pred( 'name , 'M ) ,
--                                   pred( 'output , pred( 'finished , 'M ) ) ,
--                                   pred('cv-take , termlist('M,'loc ,'None1 ) ) ,
--                                   pred('cv-take , termlist('M,'iloc ,'None2 ) ) ,
--                                   pred( 'die , nil ) ) ) ,
--                  cldef( pred( 'e , nil ) ,
--                         nil ,
--                         termlist(! , pred( 'inc , 'loc ) ,pred( 'loc , 'L ) ,
--                                  pred( 'name , 'M ) ,
--                                  pred( 'output , pred( 'at,termlist('M,'N))))))) .
-- cell want ---------------------------------------------
-- red cell( 'want , NoCVPair ,
--          clause(cldef(pred('e,nil),pred('find,'entered),
--                       termlist(!,pred('output,'someone-there),
--                       pred('subst-cell,termlist('stop,'want)))) ,
--                 cldef(pred('e,nil),nil,
--                       termlist(!,pred('enter,nil),
--                       pred('subst-cell,termlist('enter,'want)))) ,
--                 cldef(pred('enter,nil),nil,
--                       termlist(!,pred('name,'M),pred('output,pred('entering,'M)),
--                       pred('message,'enterde),
--                       pred('cv-set,termlist('M,'iloc,1))))) ) .
-- cell enter ---------------------------------------------
-- red cell( 'enter , NoCVPair ,
--          clause(cldef(pred('e,nil),pred('iloc,3),
--                       termlist(!,pred('name,'M),
--                       pred('output,pred('exiting,'M)),
--                       pred('succeed, pred('cv-take,termlist('com,'message,'None))),
--                       pred('inc,'loc),
--                       pred('subs-cell,termlist('proceed,'enter)))),
--                 cldef(pred('e,nil),nil,
--                       termlist(!,pred('inc,'iloc),pred('iloc,'LL),
--                       pred('name,'M),
--                       pred('output,pred('inside,termlist('M,'LL))))))) .

-- cell stop ---------------------------------------------
-- red cell( 'stop , NoCVPair ,
--          clause(cldef(pred('e,nil),pred('not,pred('find,'None3)),
--                       termlist(!,pred('output,'resume),
--                                pred('subst-cell,termlist('proceed,'stop)))),
--                 cldef(pred('e,nil),nil,
--                 termlist(!,pred('name,'M),pred('output,pred('waiting,'M)))))) .
-- cell main ---------------------------------------------
-- red cell('main,NoCVPair,
--         clause( cldef(pred('test,nil),nil,
--                      termlist(!,pred('fork,termlist('a,1)),
--                                 pred('fork,termlist('b,1)))) ,
--                cldef(pred('agent,termlist('M,'Loc)),nil,
--                      termlist(!,pred('new-cell,termlist('M,'loc,'iloc)),
--                               pred('push,'M),
--                               pred('or ,termlist(pred('goals ,pred('name,'M)),
--                                  pred('goals,pred('assert,pred('name,'M))))),
--                               pred('cv-write,termlist('M,'loc,'Loc)),
--                               pred('push,'proceed),
--                               pred('output,pred('initializing,termlist('M,'Loc))),
--                               pred('repeat,pred('e,nil)))) ,
--                cldef(pred('find,'Mode),nil,
--                      termlist(!,pred('cv-ref,termlist('com,'message,pred('pair,termlist('Name,'Mode)))),pred('name,'M),pred('not,pred('eq,termlist('Name,'M))))) ,
--                cldef(pred('message,'Mes),nil,
--                      termlist(!,pred('name,'M),
--                       pred('cv-write,termlist('com,'message,pred('pair,termlist('M,'Mes)))), pred('output,pred('pair,termlist('M,'Mes))))) ,
--                cldef(pred('loc,'L),nil,
--                      termlist(!,pred('name,'M),
--                      pred('cv-read,termlist('M,'loc,'L)))) ,
--                cldef(pred('iloc,'LL),nil,
--                      termlist(!,pred('name,'M),
--                       pred('cv-read , termlist('M,'iloc,'LL)))) ,
--                cldef(pred('inc,'V),termlist(pred('name,'M),
--                                    pred('cv-take,termlist('M,'V,'LV))) ,
--                      termlist(!,pred('add,termlist('LV,1,'L1)) ,
--                      pred('cv-set,termlist('M,'V,'L1)))) ,
--                cldef(pred('output,'M),nil,termlist(!,pred('write,'M))))) .

-- cell stdlib  ---------------------------------------------
-- red cell( 'stdlib,NoCVPair,
--         clause(cldef(pred('once,'Goal),nil,termlist('Goal,!)),
--                cldef(pred('success,'Goal),nil,termlist('Goal,!)),
--                cldef(pred('success,'None4),nil,nil),
--                cldef(pred('not,'Goal),pred('once,'Goal),termlist(!,fail)),
--                cldef(pred('not,'None5),nil,nil),
--                cldef(pred('or,termlist(pred('goal,'X),pred('goal,'Y))),nil,'X) ,
--                cldef(pred('or,termlist(pred('goal,'X),pred('goal,'Y))),nil,'Y) ,
--                cldef(pred('repeat,'Goal),nil,termlist(pred('repeat-try,'Goal),fail)),
--                cldef(pred('repeat-try,'Goal),pred('not,'Goal),fail),
--                cldef(pred('repeat-try,'Goal),nil,
--                      termlist(!,pred('repeat-try,'Goal))))).
-- cell system-cell ---------------------------------------------
-- red cell( 'system-cell,cvs( cvpair('a,'newa) , cvpair('b,'newb)),
--          clause(cldef(pred('cell,'proceed),nil,!) ,
--                 cldef(pred('cell,'want),nil,!) ,
--                 cldef(pred('cell,'stop),nil,!) ,
--                 cldef(pred('cell,'enter),nil,!) ,
--                 cldef(pred('cell,'main),nil,!) ,
--                 cldef(pred('cell,'stdlib),nil,!) ,
--                 cldef(pred('cell,'system-cell),nil,!) ,
--                 cldef(pred('cell,'display),nil,!) ,
--                 cldef(pred('process,'main),nil,!) )) .

-- cell display ---------------------------------------------
-- red cell( 'display , NoCVPair , NoClause ) .

-- process main ---------------------------------------------
-- red process( 'main , env('main,'stdlib,'system-cell) , loc('main,1,1) , Empty ) .

-- message deduce
-- red deduce( 'main , pred( 'test , nil ) ) .

-- state ----------------------------------------------------------

-- state( deduce('main,pred('test,nil)) ,
--           process('main,env('main,'stdlib,'system-cell),loc('main,1,1),Empty) ) .


-- red
-- state(process('main,env('main,'stdlib,'system-cell),loc('main,1,1),Empty),
--      deduce('main,termlist(pred('test,nil),pred('test,nil))) ) .


-- red belongsto( pred('test,nil) , termlist( 'fork , 'new-cell , 'push , 'assert ,
--                              'cv-write , 'cv-take , 'cv-set ,
--                              'cv-ref , 'subst-cell , 'cv-read , 'die ) ) .

-- red belongsto( pred('die,nil) , termlist( 'fork , 'new-cell , 'push , 'assert ,
--                              'cv-write , 'cv-take , 'cv-set ,
--                              'cv-ref , 'subst-cell , 'cv-read , 'die ) ) .


-- rew unify( eqn( pred('test , nil) , pred('test,nil))) .
-- rew subst( null , termlist(!,pred('fork,pred('agent,termlist('a,1))),
--                             pred('fork,pred('agent,termlist('b,1))))) .
-- rew unify( eqn( pred('fork,'T) , pred('fork,pred('agent,termlist('a,1))) ) ) .
-- rew unify( eqn( pred('agent,termlist('M,'Loc)),pred('agent,termlist('a,1)))) .
-- rew subst( sys(&&(eqn('M, 'a), eqn('Loc, 1))) ,
--           termlist(!,pred('new-cell,termlist('M,'loc,'iloc)),
--                  pred('push,'M),
--                  pred('or ,termlist(pred('goals ,pred('name,'M)),
--                  pred('goals,pred('assert,pred('name,'M))))),
--                  pred('cv-write,termlist('M,'loc,'Loc)),
--                  pred('push,'proceed),
--                  pred('output,pred('initializing,termlist('M,'Loc))),
--                  pred('repeat,pred('e,nil) ) ) ) .

-- termlist(!, pred('new-cell, termlist('a, 'loc, 'iloc)), pred('push, 'a), pred('or, termlist(pred('goals, pred('name, 'a)), pred('goals, pred('assert, pred('name, 'a))))), pred('cv-write, termlist('a, 'loc, 1)), pred('push, 'proceed), pred('output, pred('initializing, termlist('a, 1))), pred('repeat, pred('e, nil)))

-- rew  state( cell( 'system-cell , NoCVPair , NoClause ) ,
--         cprocess( 'main , env('main,'stdlib) , Meta , loc('main,1,1) , Empty ) ,
--         deduce( 'main , pred( 'new-cell , termlist('a,'loc,'iloc) ) ) ) .


-- rew state(cell('a,cvs(cvpair('loc,1),
--                 cvpair('iloc,undef)),cldef(pred('cell,'a),nil,!)),
--          cprocess('newa,env('proceed,'a,'main),Meta,loc('proceed,1,1),
--                   ctrl(pred('a,nil),loc('proceed,1,1))),
--          deduce('newa,termlist(pred('cv-read,termlist('a,'loc,5)),!))).
-- ------------------------------------------------------------------------

eof
exec state(
cell('proceed , NoCVPair , 
     clause(cldef( pred('e,nil) , 
                   pred('loc,7) ,
                   termlist(!,pred('name,'M) ,
                   pred('output,pred('want-enter,'M) ) ,
                   pred('subst-cell,termlist('want,'proceed)))),
            cldef( pred('e,nil) ,
                   pred('loc,10) ,
                   termlist(!,pred('name,'M) ,
                            pred('output,pred('finished,'M)) ,
                            pred('cv-take,termlist('M,'loc,'None1)) ,
                            pred('cv-take,termlist('M,'iloc,'None2)) ,
                            pred('die,nil)) ) ,
            cldef( pred('e,nil) ,
                   nil ,
                   termlist(!,pred('inc,'loc),pred('loc,'L) ,
                   pred('name,'M) ,
                   pred('output,pred('at,termlist('M,'L))))))) ,
cell('want , NoCVPair ,
     clause(cldef(pred('e,nil),pred('find,'entered),
                  termlist(!,pred('output,'someone-there),
                  pred('subst-cell,termlist('stop,'want)))) ,
            cldef(pred('e,nil),nil,
                  termlist(!,pred('enter,nil),
                  pred('subst-cell,termlist('enter,'want)))) ,
            cldef(pred('enter,nil),nil,
                  termlist(!,pred('name,'M),pred('output,pred('entering,'M)),
                  pred('message,'entered),
                  pred('cv-set,termlist('M,'iloc,1))))) ) ,
cell('enter , NoCVPair ,
     clause(cldef(pred('e,nil),pred('iloc,3),
                  termlist(!,pred('name,'M),
                  pred('output,pred('exiting,'M)),
                  pred('succeed, pred('cv-take,termlist('com,'message,'None))),
                  pred('inc,'loc),
                  pred('subst-cell,termlist('proceed,'enter)))),
            cldef(pred('e,nil),nil,
                  termlist(!,pred('inc,'iloc),pred('iloc,'LL),
                  pred('name,'M),
                  pred('output,pred('inside,termlist('M,'LL))))))) ,
cell('stop , NoCVPair ,
     clause(cldef(pred('e,nil),pred('not,pred('find,'None3)),
                  termlist(!,pred('output,'resume),
                  pred('subst-cell,termlist('proceed,'stop)))),
            cldef(pred('e,nil),nil,
                  termlist(!,pred('name,'M),pred('output,pred('waiting,'M)))))) ,
cell('main,NoCVPair,
     clause(cldef(pred('test,nil),nil,
                  termlist(!,pred('fork,pred('agent,termlist('a,1))),
                             pred('fork,pred('agent,termlist('b,1))),
                             pred('fork,pred('agent,termlist('c,1))))),
            cldef(pred('agent,termlist('M,'Loc)),nil,
                  termlist(!,pred('new-cell,termlist('M,'loc,'iloc)),
                  pred('push,'M),
                  pred('or ,termlist(pred('goals ,pred('name,'M)),
                  pred('goals,pred('assert,pred('name,'M))))),
                  pred('cv-write,termlist('M,'loc,'Loc)),
                  pred('push,'proceed),
                  pred('output,pred('initializing,termlist('M,'Loc))),
                  pred('repeat,pred('e,nil)))) ,
            cldef(pred('find,'Mode),nil,
                  termlist(!,pred('cv-ref,termlist('com,'message,pred('pair,termlist('Name,'Mode)))),pred('name,'M),pred('not,pred('eq,termlist('Name,'M))))) ,
            cldef(pred('message,'Mes),nil,
                  termlist(!,pred('name,'M),
                  pred('cv-write,termlist('com,'message,pred('pair,termlist('M,'Mes)))), pred('output,pred('pair,termlist('M,'Mes))))) ,
            cldef(pred('loc,'L),nil,
                  termlist(!,pred('name,'M),
                  pred('cv-read,termlist('M,'loc,'L)))) ,
            cldef(pred('iloc,'LL),nil,
                  termlist(!,pred('name,'M),
                   pred('cv-read , termlist('M,'iloc,'LL)))) ,
            cldef(pred('inc,'V),termlist(pred('name,'M),
                  pred('cv-take,termlist('M,'V,'LV))) ,
                  termlist(!,pred('add,termlist('LV,1,'L1)) ,
                  pred('cv-set,termlist('M,'V,'L1)))) ,
            cldef(pred('output,'M),nil,termlist(!,pred('write,'M))))) ,
cell( 'stdlib,NoCVPair,
     clause(cldef(pred('once,'Goal),nil,termlist('Goal,!)),
            cldef(pred('succeed,'Goal),nil,termlist('Goal,!)),
            cldef(pred('succeed,'None4),nil,nil),
            cldef(pred('not,'Goal),pred('once,'Goal),termlist(!,fail)),
            cldef(pred('not,'None5),nil,nil),
            cldef(pred('or,termlist(pred('goals,'X),pred('goals,'Y))),nil,'X) ,
            cldef(pred('or,termlist(pred('goals,'X),pred('goals,'Y))),nil,'Y) ,
            cldef(pred('repeat,'Goal),nil,termlist(pred('repeat-try,'Goal),fail)),
            cldef(pred('repeat-try,'Goal),pred('not,'Goal),fail),
            cldef(pred('repeat-try,'Goal),nil,
                  termlist(!,pred('repeat-try,'Goal))))) ,
cell( 'system-cell,cvs( cvpair('a,'newa) , cvpair('b,'newb)),
     clause(cldef(pred('cell,'proceed),nil,!) ,
            cldef(pred('cell,'want),nil,!) ,
            cldef(pred('cell,'stop),nil,!) ,
            cldef(pred('cell,'enter),nil,!) ,
            cldef(pred('cell,'main),nil,!) ,
            cldef(pred('cell,'stdlib),nil,!) ,
            cldef(pred('cell,'system-cell),nil,!) ,
            cldef(pred('cell,'display),nil,!) ,
            cldef(pred('process,'main),nil,!) )) ,
cell( 'display , NoCVPair , NoClause ) ,
cell('com,cvpair('message,undef),NoClause),
process( 'main , env('main,'stdlib,'system-cell) , loc('main,1,1) , 
          pred( 'test , nil ),Empty ) ) .

