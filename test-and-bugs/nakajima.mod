-- From: nakajima@swl.cl.nec.co.jp
-- Date: Tue, 30 Sep 1997 09:34:41 +0900 (JST)
-- Message-Id: <199709300034.JAA27923@ruby.swl.cl.nec.co.jp>
-- To: sawada@sra.co.jp
-- Subject: CafeOBJ Spec of Trader
-- Cc: nakajima@ccm.cl.nec.co.jp
-- Content-Type: text
-- Content-Length: 41958


-- 澤田さま


--    先のWGで話題になった「ODPトレーダ仕様」です。

--    インタプリタ版CafeOBJの修正確認のための
--    「テストデータ」としてお使い下さい。

--    また、同時に、以下をお願い致します。
--    (1) 記述上の問題、等を発見された場合は、
--        連絡して下さい。当方も、勉強したいので ...
--    (2) コンパイラ版のテストデータにも使って下さい。
--        特に、コンパイラ版が仮定している諸元の制約の
--        範囲に収まっているか不安です。

--    よろしくお願い致します。

--    まだ、未完成と思っています。上の用途、以外に
--    使われようとする場合は、御一報願います。


--    -- なかじま (NEC)


-- ==================== CUT ==========================
! date
--  Basic Utility Modules


mod* TRIV2 {
  [ Elt2 ]
}

mod! COLLECTION[X :: TRIV] {
  [ Collection,  NeCollection ]
  [ Elt < NeCollection < Collection ]

  signature {
    op nil : -> Collection  
    op __ : Collection Collection -> Collection {assoc id: nil}
    op __ : NeCollection Collection -> NeCollection 
    op __ : NeCollection NeCollection -> NeCollection  
  }

  protecting (NAT)

  signature {
    op |_| : Collection -> Nat
    op is-empty : Collection -> Bool
  }

  axioms {
    var E : Elt
    var L : Collection

    eq | nil | = 0  .
    eq | E   | = 1 .
    eq | E L | = 1 + | L |  .

    eq is-empty(L) =  (L == nil) .
  }

  signature {
    op _is-subsumed-by_ : Collection Collection -> Bool
    op isb-outer : Collection Collection -> Bool
    op isb-inner : Elt Collection -> Bool

    op _cap_ : Collection Collection -> Collection
    op cap-outer : Collection Collection Collection -> Collection
    op cap-inner : Elt Collection Collection -> Collection

    op _equal-to_ : Collection Collection -> Bool
    op eq-outer : Collection Collection -> Bool
    op eq-inner : Collection Collection -> Bool

    op _cup_ : Collection Collection -> Collection
    op cup-exec : Collection Collection -> Collection

    op copy : Collection -> Collection
    op copy-exec : Collection Collection -> Collection

    op rev  : Collection -> Collection
    op rev-exec : Collection Collection -> Collection

    op _is-member-of_ : Elt Collection -> Bool
    op imo-exec : Collection Elt -> Bool

    op add : Collection Elt -> Collection
    op delete : Collection Elt -> Collection
    op del-exec : Collection Elt Collection -> Collection
    op override : Collection Elt Elt -> Collection
    op ov-exec  : Collection Elt Elt Collection -> Collection
  }

  axioms {
    vars X X1 X2 Y : Elt
    vars L1 L2 : Collection

    eq (L1) is-subsumed-by (L2) = isb-outer (L1, L2) .
    eq isb-outer(nil, L) = true .
    eq isb-outer(X1,L) = isb-inner(X1, L) .
    eq isb-outer((X1 L1), L)
    =  if isb-inner(X1, L) then isb-outer(L1, L) else false fi .
    eq  isb-inner(X, nil)  = false .
    eq  isb-inner(X, X2)   = (X == X2) .
    ceq isb-inner(X, (X2 L2)) = true  if X == X2 .
    ceq isb-inner(X, (X2 L2)) = isb-inner(X, L2) if not(X == X2) .

    eq (L1) cap (L2) = cap-outer(L1, L2, nil) .
    eq cap-outer(nil, L2, L) = L .
    eq cap-outer(X1,L2,L)    = cap-inner(X1,L2,L) .
    eq cap-outer((X1 L1), L2, L) = cap-outer(L1, L2, cap-inner(X1, L2, L)) .
    eq  cap-inner(X, nil, L) = L .
    ceq  cap-inner(X, X2,  L) = (X L) if X == X2 .
    ceq  cap-inner(X, X2,  L) = L if not(X == X2)  .
    ceq cap-inner(X, (X2 L2), L) = (X L) if X == X2 .
    ceq cap-inner(X, (X2 L2), L) = cap-inner(X,L2,L) if not(X == X2) .
    
    eq copy(L) = rev(copy-exec(L,nil)) .
    eq copy-exec(nil, L) = L .
    eq copy-exec(X1, L)  = (X1 L) .
    eq copy-exec((X1 L1), L2) = copy-exec(L1, (X1 L2)) .

    eq rev(L) = rev-exec(L,nil) .
    eq rev-exec(nil, L) = L .
    eq rev-exec(X1,L)   = (X1 L) .
    eq rev-exec((X1 L1), L) = rev-exec(L1, (X1 L)) .

    eq (X) is-member-of (L) = imo-exec(L,X) .
    eq  imo-exec(nil, X)    = false .
    eq  imo-exec(X1, X)     = (X1 == X) .
    ceq imo-exec((X1 L1),X) = true           if (X1 == X) .
    ceq imo-exec((X1 L1),X) = imo-exec(L1,X) if not (X1 == X) .

    eq (L1) cup (L2) = cup-exec(L1,copy(L2)) .
    eq cup-exec(nil,L2) = L2 .
    eq cup-exec(X1,L2)
    =  if ((X1) is-member-of (L2)) then L2 else (X1 L2) fi .
    eq cup-exec((X1 L1),L2)
    =  if ((X1) is-member-of (L2)) then cup-exec(L1,L2)
       else cup-exec(L1,(X1 L2)) fi .

    eq (nil) equal-to (nil) = true .
    eq (L1)  equal-to (L2)
    =  if (| L1 | == | L2 |) then eq-outer(L1,L2) else false fi .
    eq eq-outer(nil, L2) = true .
    eq eq-outer(X1,L2)   = eq-inner(X1,L2) .
    eq eq-outer((X1 L1), L2)
    =  if eq-inner(X1, L2) then eq-outer(L1, L2) else false fi .
    eq eq-inner(X, nil) = false .
    eq eq-inner(X, X2) = (X == X2) .
    ceq eq-inner(X, (X2 L2)) = true if X == X2 .
    ceq eq-inner(X, (X2 L2)) = eq-inner(X,L2) if not (X == X2) .

    eq add(L,X) = (X L) .

    eq  delete(L, X)    = del-exec(L, X, nil) .
    eq  del-exec(nil, X, L2) = rev(L2) .
    ceq  del-exec(X1, X, L2) = del-exec(nil,X,(X1 L2)) if not(X1 == X) .
    ceq  del-exec(X1, X, L2) = (rev(L2)) if (X1 == X) .
    ceq del-exec((X1 L1),X,L2) = del-exec(L1,X,(X1 L2)) if not(X1 == X) .
    ceq del-exec((X1 L1),X,L2) = ((rev(L2)) L1) if (X1 == X) .

    eq override(L,X,Y) = ov-exec(L,X,Y,nil) .
    eq ov-exec(nil,X,Y,L2) = rev(L2)  .
    ceq ov-exec(X1,X,Y,L2) = ov-exec(nil,X,Y,(X1 L2)) if not(X1 == X) .
    ceq ov-exec(X1,X,Y,L2) = ((rev(L2)) Y) if X1 == X .
    ceq ov-exec((X1 L1),X,Y,L2) = ov-exec(L1,X,Y,(X1 L2)) if not(X1 == X) .
    ceq ov-exec((X1 L1),X,Y,L2) = ((rev (L2)) (Y L1)) if X1 == X .
  }
}


mod! TUPLE[X :: TRIV, Y :: TRIV2] {
  protecting (2TUPLE[X,Y]*{ sort 2Tuple -> Tuple })

  signature {
    op _===_ : Tuple Tuple -> Bool
  }
  axioms {
    vars T1 T2 : Tuple

    eq (T1) === (T2) = ((1* T1) == (1* T2)) and ((2* T1) == (2* T2))  .
  }
}

--


mod! ELEMENT[X1 :: TRIV, Y1 :: TRIV2] {
  using (TUPLE[X1,Y1] * { sort Tuple -> KeyValue,
			  op (<<_;_>>) -> ({_,_}) } )
}


mod! ENVIRONMENT[X1 :: TRIV, Y2 :: TRIV2] {
  using (COLLECTION[X <= view to ELEMENT[X1,Y2] { sort Elt -> KeyValue }]
	 * { sort Collection -> Environment,
	     sort NeCollection -> NeEnvironment,
	     op nil -> empty })

  signature {
    op add : Environment Elt.X1 Elt2.Y2 -> Environment
    op add-exec : Environment Elt.X1 Elt2.Y2 Environment -> Environment
    op delete : Environment Elt.X1 -> Environment
    op del-exec : Environment Elt.X1 Environment -> Environment
    op override : Environment Elt.X1 Elt2.Y2 -> Environment
    op ov-exec : Environment Elt.X1 Elt2.Y2 Environment -> Environment
    op lookup : Environment Elt.X1 -> Elt2.Y2
  }

  axioms {
    vars T T1 : KeyValue
    vars L L1 L2 : Environment
    var XX : Elt.X1 
    var YY : Elt2.Y2

    eq add(L,XX,YY) = add-exec(L,XX,YY,empty) .
    eq add-exec(empty,XX,YY,L2) = (({(XX),(YY)}) (rev(L2))) .
    ceq add-exec(T1,XX,YY,L2)    = add-exec(empty,XX,YY,(T1 L2)) 
    if not((1*(T1)) == XX) .
    ceq add-exec(T1,XX,YY,L2)    = (rev(L2) ({(XX),(YY)}))
    if ((1*(T1)) == XX) .
    ceq add-exec((T1 L1),XX,YY,L2) = add-exec(L1,XX,YY,(T1 L2))
    if not((1*(T1)) == XX) .
    ceq add-exec((T1 L1),XX,YY,L2) = (rev(L2) (({(XX),(YY)}) L1))
    if ((1*(T1)) == XX) .

    eq delete(L,XX) = del-exec(L,XX,empty) .
    eq del-exec(empty,XX,L2) = rev(L2) .
    ceq del-exec(T1,XX,L2) = del-exec(empty,XX,(T1 L2))
    if not((1*(T1)) == XX) .
    ceq del-exec(T1,XX,L2) = rev(L2)
    if ((1*(T1)) == XX) .
    ceq del-exec((T1 L1),XX,L2) = del-exec(L1,XX,(T1 L2))
    if not((1*(T1)) == XX) .
    ceq del-exec((T1 L1),XX,L2) = (rev(L2) L1) 
    if (1*(T1)) == XX .

    eq override(L,XX,YY) = ov-exec(L,XX,YY,empty) .
    eq ov-exec(empty,XX,YY,L2) = (({(XX),(YY)}) rev(L2)) .
    ceq ov-exec(T1,XX,YY,L2) = ov-exec(empty,XX,YY,(T1 L2))
    if not((1*(T1)) == XX) .
    ceq ov-exec(T1,XX,YY,L2) = (rev(L2) ({(XX),(YY)}))
    if ((1*(T1)) == XX) .
    ceq ov-exec((T1 L1),XX,YY,L2) = ov-exec(L1,XX,YY,(T1 L2))
    if not((1*(T1)) == XX) .
    ceq ov-exec((T1 L1),XX,YY,L2) = ((rev(L2)) ({(XX),(YY)} L1))
    if ((1*(T1)) == XX) .

--  eq lookup(empty,XX) 

    ceq lookup(T1,XX)      = lookup(empty,XX) if not((1*(T1)) == XX) .
    ceq lookup(T1,XX)      = 2*(T1)        if (1*(T1)) == XX .
    ceq lookup((T1 L1),XX) = lookup(L1,XX) if not((1*(T1)) == XX) .
    ceq lookup((T1 L1),XX) = 2*(T1)        if (1*(T1)) == XX .
  }
}


mod* INTERFACES {
  [ InterfaceSignatureType  InterfaceIdentifier  ]
}

mod* THE-INTERFACES {
  extending (INTERFACES)

  signature {
    op ist : -> InterfaceSignatureType
    op iid : -> InterfaceIdentifier
    op iid0 : -> InterfaceIdentifier
    op iid1 : -> InterfaceIdentifier
    op iid2 : -> InterfaceIdentifier
  }
}

-- 7.2.2 Properties
--

mod* NAME {
  [ Name ]
}

mod* THE-NAME {
  protecting (NAME)
  protecting (QID)
  [ Id < Name ]
}


view TRIV2NAME from TRIV to THE-NAME {
  sort Elt -> Name
}


mod* THE-NAMES   principal-sort Names {
  protecting (COLLECTION[TRIV2NAME]
	      *{ sort Collection -> Names,
		 sort NeCollection -> NeNames })
}


-- Value and ValueType

mod* VALUE {
  [ Value ]
}


mod* VALUE-TYPE {
  [ ValueType ]
}

mod* TOP-VALUE-VALUETYPE {
  extending (VALUE)
  extending (VALUE-TYPE)
  signature {
    op type : Value -> ValueType
    op Value : -> ValueType
  }
}


mod* INT-VALUE-VALUETYPE {
  [ ValueInt ]
  extending (TOP-VALUE-VALUETYPE)
  [ ValueInt < Value ]
  signature {
    op type : ValueInt -> ValueType 
    op ValueInt : -> ValueType
  }
  axioms {
    var V : ValueInt
    var T : ValueType

    eq type(V) = ValueInt .
  }
}

mod* THE-INT-VALUE-VALUETYPE {
  extending (INT-VALUE-VALUETYPE)
  protecting (INT)

  [ Int < ValueInt ]
}


mod* THE-ALL-VALUE-VALUETYPE {
  protecting (TOP-VALUE-VALUETYPE)
  protecting (THE-INT-VALUE-VALUETYPE)
}

view TRIV2VALUE-TYPE from TRIV to VALUE-TYPE {
  sort Elt -> ValueType
}

mod* THE-VALUES {
  protecting (THE-ALL-VALUE-VALUETYPE)
  protecting (COLLECTION[TRIV2VALUE-TYPE]
	      *{ sort Collection -> ValueTypes,
		 sort NeCollection -> NeValueTypes })

  signature {
    op supers : ValueType -> ValueTypes
    op one-of : ValueType ValueTypes -> Bool
  }

  axioms {
    vars X Y : ValueType
    var L : ValueTypes

    eq supers(Value)    = (Value nil) .
    eq supers(ValueInt) = (ValueInt Value nil) .

    eq  one-of(X, nil)   = false .
    ceq one-of(X, (Y L)) = true  if X == Y .
    ceq one-of(X, (Y L)) = one-of(X, L) if not(X == Y) .
  }
}


view TRIV2THEVALUE from TRIV2 to THE-VALUES {
  sort Elt2 -> Value
}

view TRIV2THEVALUETYPE from TRIV to THE-VALUES {
  sort Elt -> ValueType
}


-- 7.2.3 Service Type
--

mod* MODE {
  [ Mode ]
  signature {
    ops normal readonly mandatory readonlymandatory : -> Mode
  }
}

view TRIV2MODE from TRIV to MODE {
  sort Elt -> Mode
}

view TRIV22MODE from TRIV2 to MODE {
  sort Elt2 -> Mode
}

mod* VALUETYPE-MODE {
  protecting (TUPLE[TRIV2THEVALUETYPE,TRIV22MODE]
	      *{ sort Tuple -> ValueMode,
		 op (1*_) -> get-value-type,
		 op (2*_) -> get-mode })
}

view TRIV2VALUETYPE-MODE from TRIV2 to VALUETYPE-MODE {
  sort Elt2 -> ValueMode
}


mod! TH-ENV {
  protecting (THE-NAMES)

  [ NeEnv Env ]
  [ Binding ]
  [ Binding < NeEnv < Env ]

  signature {
    op empty : -> Env
    op __ : Env     Env -> Env
    op __ : NeEnv   Env -> NeEnv
    op __ : NeEnv   NeEnv -> NeEnv
    op key : Binding -> Name
  }
}

mod* COLLECT-NAMES[X :: TH-ENV] {
  signature {
    op names : Env -> Names
    op name-exec : Env Names -> Names
  }
  axioms {
    var B : Binding
    var L : Env
    var N : Names

    eq names(L) = name-exec(L,nil) .
    eq name-exec(empty,N) = rev(N) .
    eq name-exec((B L),N) = name-exec(L, (key(B) N)) .
  }
}


mod* THE-PROPERTY-DEFINITIONS {
  protecting (ENVIRONMENT[TRIV2NAME,TRIV2VALUETYPE-MODE]
	      *{ sort Environment -> PropertyDefinitions,
		 sort NeEnvironment -> NePropertyDefinitions,
		 sort KeyValue -> PropertyDefinition })

  protecting (THE-NAMES)

  signature {
    op names : PropertyDefinitions -> Names
    op name-exec : PropertyDefinitions Names -> Names
  }

  axioms {
    var T : PropertyDefinition
    var L : PropertyDefinitions
    var N : Names

    eq names(L) = name-exec(L,nil) .
    eq name-exec(empty,N) = rev(N) .
    eq name-exec((T L),N) = name-exec(L,((1*(T)) N)) .
  }
}


mod* THE-PROPERTY-VALUES {
  protecting (ENVIRONMENT[TRIV2NAME, TRIV2THEVALUE]
	      *{ sort Environment -> PropertyValues,
		 sort NeEnvironment -> NePropertyValues,
		 sort KeyValue -> Property,
		 op ({_,_}) -> ({_;_}) })
  protecting (THE-NAMES)

  signature {
    op names : PropertyValues -> Names
    op name-exec : PropertyValues Names -> Names
  }

  axioms {
    var T : Property
    var L : PropertyValues
    var N : Names

    eq names(L) = name-exec(L,nil) .
    eq name-exec(empty,N) = rev(N) .
    eq name-exec((T L),N) = name-exec(L,((1*(T)) N)) .
  }
}


mod* THE-SERVICE-TYPE {
  [ ServiceType  ]
  protecting (THE-PROPERTY-DEFINITIONS)
  protecting (THE-INTERFACES)

  signature {
    op [signature=_, prop-defs=_] :
      InterfaceSignatureType PropertyDefinitions -> ServiceType
    op _.signature : ServiceType -> InterfaceSignatureType 
    op _.prop-defs : ServiceType -> PropertyDefinitions
    op mk-service-type : 
      InterfaceSignatureType PropertyDefinitions -> ServiceType
  }

  axioms {
    var S : InterfaceSignatureType
    var P : PropertyDefinitions

    eq [signature=(S), prop-defs=(P)].signature = S .
    eq [signature=(S), prop-defs=(P)].prop-defs = P .
    eq mk-service-type(S,P)  = [signature=(S), prop-defs=(P)] .
  }
}


-- filter style functions

mod! FILTER1 {
  protecting (VALUETYPE-MODE)
  signature {
    op filter1 : ValueMode -> Bool
  }
}

mod! FILTER2 {
  protecting (VALUETYPE-MODE)
  signature {
    op filter2 : ValueMode -> Bool
  }
}

mod* COLLECTOR[X :: FILTER1, Y :: FILTER2] {
  protecting (THE-PROPERTY-DEFINITIONS)

  signature {
    op collect1  : PropertyDefinitions -> Names
    op col-eval1 : PropertyDefinitions Names -> Names

    op collect2  : PropertyDefinitions -> Names
    op col-eval2 : PropertyDefinitions Names -> Names
  }

  axioms {
    var T : PropertyDefinition
    var L : PropertyDefinitions 
    var N : Names

    eq collect1 (L) = col-eval1(L,nil) .
    eq col-eval1(empty,N) = rev(N) .
    eq col-eval1((T L),N) =
      if filter1(2*(T)) then col-eval1(L,((1*(T)) N)) else col-eval1(L,N) fi .

    eq collect2 (L) = col-eval2(L,nil) .
    eq col-eval2(empty,N) = rev(N) .
    eq col-eval2((T L),N) =
      if filter2(2*(T)) then col-eval2(L,((1*(T)) N)) else col-eval2(L,N) fi .
  }
}

mod* THE-SERVICE-TYPE-FILTER {
  protecting (VALUETYPE-MODE)

  signature {
    op filter-mandatory : ValueMode -> Bool
    op filter-readonly  : ValueMode -> Bool
    op is-mandatory : Mode -> Bool
    op is-readonly : Mode -> Bool
  }

  axioms {
    var D : ValueMode
    var M : Mode

    eq is-mandatory(M) = (M == mandatory) or (M == readonlymandatory)  .
    eq is-readonly(M)  = (M == readonly) or  (M == readonlymandatory)  .

    eq filter-mandatory(D) = is-mandatory(get-mode(D))  .
    eq filter-readonly(D)  = is-readonly(get-mode(D))  .
  }
}

view FILTER-MANDATORY from FILTER1 to THE-SERVICE-TYPE-FILTER {
  op filter1 -> filter-mandatory
}

view FILTER-READONLY from FILTER2 to THE-SERVICE-TYPE-FILTER {
  op filter2 -> filter-readonly
}


mod* THE-SERVICE-TYPE-PROPERTIES {

  protecting (COLLECTOR[FILTER-MANDATORY,FILTER-READONLY]
	      *{ op collect1 -> collect-mandatory,
		 op collect2 -> collect-readonly })
  protecting (THE-SERVICE-TYPE)

  signature {
    op mandatory-props : ServiceType -> Names
    op readonly-props  : ServiceType -> Names
  }
  axioms {
    var S : ServiceType

    eq mandatory-props(S) = collect-mandatory((S).prop-defs)  .
    eq readonly-props(S)  = collect-readonly((S).prop-defs)  .
  }
}

-- 7.2.4 Service Type Subtyping Rules
--

mod* SIGNATURE-SUBTYPING {
  protecting (THE-INTERFACES)
  signature {
    op _is-sig-subtype-of_ : 
      InterfaceSignatureType InterfaceSignatureType -> Bool
  }
}

mod* THE-SIGNATURE-SUBTYPING {
  extending (SIGNATURE-SUBTYPING)
  axioms {
    vars I1 I2 : InterfaceSignatureType

    eq (I1) is-sig-subtype-of (I2) = true .
  }
}

mod* VALUE-SUPERTYPING-RELATION {
  protecting (THE-VALUES)
  signature {
    op _is-value-supertype-of_ : ValueType ValueType -> Bool
  }
}

mod* THE-VALUE-SUPERTYPING-RELATION {
  extending (VALUE-SUPERTYPING-RELATION)
  axioms {
    vars T1 T2 : ValueType

    eq (T1) is-value-supertype-of (T2) = one-of(T1, supers(T2)) .
  }
}


-- The module MODE is defined in iv-1.obj


mod* MODE-PAIR {
  protecting (TUPLE[TRIV2MODE,TRIV22MODE]*{ sort Tuple -> ModePair })
}

view TRIV2MODEPAIR from TRIV to MODE-PAIR {
  sort Elt -> ModePair
}

mod* THE-MODE-SUPERTYPING-RELATION {
  protecting (COLLECTION[TRIV2MODEPAIR]
	      *{ sort Collection -> ModeRelations,
		 sort NeCollection -> NeModeRelations })
  signature {
    op _is-mode-supertype-of_ : Mode Mode -> Bool
    op MR : -> ModeRelations
  }
  axioms {
    vars M1 M2 : Mode

    eq MR = (<<(normal);(readonly)>> <<(normal);(mandatory)>>
	       <<(normal);(readonlymandatory)>> <<(readonly);(readonlymandatory)>>
		 <<(mandatory);(readonlymandatory)>>) .
    eq (M1) is-mode-supertype-of (M2) = (<<(M1);(M2)>>) is-subsumed-by MR .
  }
}

--

mod! VALUE-MODE-SUPERTYPE-PRED {
  protecting (THE-PROPERTY-DEFINITIONS)
  signature {
    op p : Name PropertyDefinitions PropertyDefinitions -> Bool
  }
}

mod* VALUE-MODE-SUPERTYPE-FLATTEN[P :: VALUE-MODE-SUPERTYPE-PRED] {
  signature {
    op flatten : Names PropertyDefinitions PropertyDefinitions -> Bool
  }
  axioms {
    var N : Name
    var L : Names
    vars P1 P2 : PropertyDefinitions

    eq flatten(nil,P1,P2) = true .
    eq flatten((N L),P1,P2)
    =  if p(N,P1,P2) then flatten(L,P1,P2) else false fi .
  }
}

mod* PREDICATE-VALUE-MODE {
  protecting (THE-PROPERTY-DEFINITIONS)
  protecting (THE-VALUE-SUPERTYPING-RELATION)
  protecting (THE-MODE-SUPERTYPING-RELATION)

  signature {
    op pred-vm : Name PropertyDefinitions PropertyDefinitions -> Bool
    op pvm : ValueMode ValueMode -> Bool
  }

  axioms {
    var N : Name
    vars P1 P2 : PropertyDefinitions
    vars W1 W2 : ValueMode

    eq pred-vm (N,P1,P2) = pvm(lookup(P1,N), lookup(P2,N)) .
    eq pvm(W1,W2)
    = (((get-value-type(W1)) is-value-supertype-of (get-value-type(W2))))
    and (((get-mode(W1)) is-mode-supertype-of (get-mode(W2)))) .
  }
}

view PRED2SUBTYPING from VALUE-MODE-SUPERTYPE-PRED to PREDICATE-VALUE-MODE {
  op p -> pred-vm
}

mod* THE-SUBTYPING-RULE {
  protecting (THE-SERVICE-TYPE)
  protecting (THE-SIGNATURE-SUBTYPING)
  protecting (VALUE-MODE-SUPERTYPE-FLATTEN[PRED2SUBTYPING]
	      *{ op flatten -> check-vm })

  signature {
    op _is-subtype-of_ : ServiceType ServiceType -> Bool
  }

  axioms {
    vars S1 S2 : ServiceType

    eq (S1) is-subtype-of (S2)
    =     ((S1).signature) is-sig-subtype-of ((S2).signature)
    and ((names((S1).prop-defs)) is-subsumed-by (names((S2).prop-defs)))
    and check-vm(names((S1).prop-defs), (S1).prop-defs, (S2).prop-defs) .
  }
}



-- 7.2.5 Service Offer
--


mod! SERVICE-OFFER-PRED {
  protecting (THE-PROPERTY-DEFINITIONS)
  protecting (THE-PROPERTY-VALUES)
  protecting (THE-VALUE-SUPERTYPING-RELATION)
  protecting (THE-MODE-SUPERTYPING-RELATION)
  signature {
    op p : Name PropertyValues PropertyDefinitions -> Bool
  }
}

mod* SERVICE-OFFER-FLATTEN[P :: SERVICE-OFFER-PRED] {
  signature {
    op flatten : Names PropertyValues PropertyDefinitions -> Bool
  }
  axioms {
    var N : Name
    var L : Names
    var Q : PropertyValues
    var P : PropertyDefinitions

    eq flatten(nil,Q,P)   = true .
    eq flatten((N L),Q,P) =  if p(N,Q,P) then flatten(L,Q,P) else false fi .
  }
}

mod* PREDICATE-SERVICE-OFFER {
  protecting (THE-PROPERTY-DEFINITIONS)
  protecting (THE-PROPERTY-VALUES)
  protecting (THE-VALUE-SUPERTYPING-RELATION)
  protecting (THE-MODE-SUPERTYPING-RELATION)

  signature {
    op pred-so : Name PropertyValues PropertyDefinitions -> Bool
    op pso : Value ValueType -> Bool
  }
  axioms {
    var N : Name
    var Q : PropertyValues
    var P : PropertyDefinitions
    var V : Value
    var T : ValueType

    eq pred-so (N,Q,P) = pso(lookup(Q,N), get-value-type(lookup(P,N))) .
    eq pso(V,T) = one-of (T, supers(type(V))) .
  }
}


view PRED2SO from SERVICE-OFFER-PRED to PREDICATE-SERVICE-OFFER {
  op p -> pred-so
}

-- Super sorts of all the return values (1997.6.25)

mod* RETURN-VALUE {
  [ ReturnValue ]
  signature {
    op void : -> ReturnValue
  }
}

mod* SERVICE-OFFER-ID {
  extending (RETURN-VALUE)
  [ ServiceOfferIdentifier ]
  [ ServiceOfferIdentifier < ReturnValue ]
  signature {
    op NoId : -> ServiceOfferIdentifier
  }
}

mod* THE-SERVICE-OFFER-ID {
  extending (SERVICE-OFFER-ID)
  protecting (NAT)
  [ Nat < ServiceOfferIdentifier ]
}


mod* SERVICE-OFFER {
  [ ServiceOffer ]

  protecting (THE-PROPERTY-VALUES)
  protecting (THE-SERVICE-OFFER-ID)
  protecting (THE-SERVICE-TYPE)

  signature {
    op new-service-offer :
      ServiceType PropertyValues InterfaceIdentifier ServiceOfferIdentifier
	-> ServiceOffer

    op [service-type=_, prop-vals=_, interface-id=_, offer-id=_] : 
      ServiceType PropertyValues InterfaceIdentifier ServiceOfferIdentifier
	-> ServiceOffer
    op _.service-type : ServiceOffer -> ServiceType
    op _.prop-vals    : ServiceOffer -> PropertyValues
    op _.interface-id : ServiceOffer -> InterfaceIdentifier
    op _.offer-id     : ServiceOffer -> ServiceOfferIdentifier
  }

  axioms {
    var S : ServiceType
    var Q : PropertyValues
    var I : InterfaceIdentifier
    var O : ServiceOfferIdentifier
      
    eq [service-type=(S), prop-vals=(Q), interface-id=(I), offer-id=(O)].service-type  =  S  .
    eq [service-type=(S), prop-vals=(Q), interface-id=(I), offer-id=(O)].prop-vals     =  Q  .
    eq [service-type=(S), prop-vals=(Q), interface-id=(I), offer-id=(O)].interface-id  =  I  .
    eq [service-type=(S), prop-vals=(Q), interface-id=(I), offer-id=(O)].offer-id      =  O  .

    eq new-service-offer(S,Q,I,O)
    = [service-type=(S), prop-vals=(Q), interface-id=(I), offer-id=(O)] .
  }
}

mod* SERVICE-OFFER-AXIOMS {
  protecting (SERVICE-OFFER)
  protecting (THE-SERVICE-TYPE-PROPERTIES)
  protecting (SERVICE-OFFER-FLATTEN[PRED2SO]*{ op flatten -> soa3 })

  signature {
    op service-offer-axioms : ServiceOffer -> Bool
    op soa0 : ServiceType PropertyValues -> Bool
    op soa2 : ServiceType PropertyDefinitions PropertyValues -> Bool
  }

  axioms {
    var V : ServiceOffer
    vars L L1 L2 : Names
    var Q : PropertyValues
    var N : Name
    var S : ServiceType
    var P : PropertyDefinitions

    eq service-offer-axioms(V) = soa0((V).service-type,(V).prop-vals) .
    eq soa0(S,Q)   = soa2(S,(S).prop-defs,Q) .
    eq soa2(S,P,Q) = (mandatory-props(S)) is-subsumed-by (names(Q))
    and soa3(((names(P)) cap (names(Q))), Q, P) .
  }
}


-- 7.2.6 Criteria and Constraints
--

view TRIV2OFFER from TRIV to SERVICE-OFFER {
  sort Elt -> ServiceOffer
}

mod* SERVICE-OFFERS {
  protecting (COLLECTION[TRIV2OFFER]
	      *{ sort Collection -> ServiceOffers,
		 sort NeCollection -> NeServiceOffers })
  extending (RETURN-VALUE)
  [ ServiceOffers < ReturnValue ]
}


-- 7.3 Invariant Schema
--

mod* NODE {
  [ Node ]
}

mod* THE-NODE {
  protecting (NODE)
  protecting (QID)
  [ Id < Node ]
}

view TRIV2NODE from TRIV to THE-NODE {
  sort Elt -> Node
}

view TRIV22NODE from TRIV2 to THE-NODE {
  sort Elt2 -> Node
}


mod* NODE-S {
  protecting (COLLECTION[TRIV2NODE]
	      *{ sort Collection -> Nodes,
		 sort NeCollection -> NeNodes })
}

mod* EDGE {
  protecting (TUPLE[TRIV2NODE,TRIV22NODE]
	      *{ sort Tuple -> Edge,
		 op (1*_) -> src,
		 op (2*_) -> dest })

  signature {
    op edge : Node Node -> Edge
  }

  axioms {
    vars N1 N2 : Node

    eq edge(N1,N2) = <<(N1);(N2)>> .
  }
}

view TRIV2EDGE from TRIV to EDGE {
  sort Elt -> Edge
}

mod* EDGE-S {
  protecting (COLLECTION[TRIV2EDGE]*{ sort Collection -> Edges })
}

mod* PARTITION-S {
  protecting (ENVIRONMENT[TRIV2OFFER, TRIV22NODE]
	      *{ sort Environment -> Partitions,
		 sort NeEnvironment -> NePartitions,
		 sort KeyValue -> Partition })
}


view TRIV2PROPVALUES from TRIV2 to THE-PROPERTY-VALUES {
  sort Elt2 -> PropertyValues
}


mod* EDGE-PROPERTIES {
  protecting (ENVIRONMENT[TRIV2EDGE, TRIV2PROPVALUES]
	      *{ sort Environment -> EdgeProperties,
		 sort NeEnvironment -> NeEdgeProperties,
		 sort KeyValue -> EdgeProperty })
--          op {_,_} -> [_;_] })
}


mod* TRADING-SYSTEM {
  [ TradingSystem ]
  protecting (SERVICE-OFFERS)
  protecting (NODE-S)
  protecting (EDGE-S)
  protecting (PARTITION-S)
  protecting (EDGE-PROPERTIES)

  signature {
    op new-trading-system :
      ServiceOffers Nodes Partitions Edges EdgeProperties -> TradingSystem
    op [offers=_, nodes=_, partition=_, edges=_, edge-properties=_] :
      ServiceOffers Nodes Partitions Edges EdgeProperties -> TradingSystem
    op _.offers : TradingSystem -> ServiceOffers
    op _.nodes  : TradingSystem -> Nodes
    op _.partition  : TradingSystem -> Partitions
    op _.edges  : TradingSystem -> Edges
    op _.edge-properties  : TradingSystem -> EdgeProperties
  }

  axioms {
    var S : ServiceOffers
    var N : Nodes
    var P : Partitions
    var E : Edges
    var Q : EdgeProperties

    eq [offers=(S), nodes=(N), partition=(P), edges=(E), edge-properties=(Q)].offers  = S .
    eq [offers=(S), nodes=(N), partition=(P), edges=(E), edge-properties=(Q)].nodes   = N .
    eq [offers=(S), nodes=(N), partition=(P), edges=(E), edge-properties=(Q)].partition   = P .
    eq [offers=(S), nodes=(N), partition=(P), edges=(E), edge-properties=(Q)].edges   = E .
    eq [offers=(S), nodes=(N), partition=(P), edges=(E), edge-properties=(Q)].edge-properties   = Q .
    
    eq new-trading-system(S,N,P,E,Q)
    = [offers=(S), nodes=(N), partition=(P), edges=(E), edge-properties=(Q)] .
  }
}



mod* TRADING-SYSTEM-LIBRARY {
  protecting (PARTITION-S)
  protecting (SERVICE-OFFERS)
  protecting (NODE-S)
  protecting (EDGE-S)
  protecting (EDGE-PROPERTIES)

  signature {
    op dom-partition : Partitions -> ServiceOffers
    op dom-par-exec  : Partitions ServiceOffers -> ServiceOffers
      
    op ran-partition : Partitions -> Nodes
    op ran-par-exec  : Partitions Nodes -> Nodes

    op all-nodes-of  : Edges -> Nodes
    op dom-edges : Edges Nodes -> Nodes
    op ran-edges : Edges Nodes -> Nodes

    op dom-edge-prop : EdgeProperties -> Edges
    op dom-edge-prop-exec : EdgeProperties Edges -> Edges
  }

  axioms {
    var L : Partitions
    var T : Partition
    var S : ServiceOffers 
    var N : Nodes
    var E : Edges 
    var X : Edge
    var F : EdgeProperties
    var Y : EdgeProperty

    eq dom-partition(L) = dom-par-exec(L,nil) .
    eq dom-par-exec(empty, S) = rev(S) .
    eq dom-par-exec((T L), S) = dom-par-exec(L, ((1*(T)) S)) .

    eq ran-partition(L) = ran-par-exec(L,nil) .
    eq ran-par-exec(empty, N) = rev(N) .
    eq ran-par-exec((T L), N) = ran-par-exec(L, ((2*(T)) N)) .
    
    
    eq all-nodes-of (E) = (dom-edges(E,nil)) cup (ran-edges(E,nil)) .
    eq dom-edges(nil, N) = N .
    eq dom-edges((X E), N) = dom-edges(E, (src(X) N)) .
    eq ran-edges(nil, N) = N .
    eq ran-edges((X E), N) = ran-edges(E, (dest(X) N)) .

    eq dom-edge-prop(F) = dom-edge-prop-exec(F,nil) .
    eq dom-edge-prop-exec(empty,E) = E .
    eq dom-edge-prop-exec((Y F),E) = dom-edge-prop-exec(F,((1*(Y)) E)) .
  }
}


mod* TRADING-SYSTEM-AXIOMS {
  protecting (TRADING-SYSTEM)
  protecting (TRADING-SYSTEM-LIBRARY)

  signature {
    op trading-system-axiom : TradingSystem -> Bool
    op service-offer-equality : ServiceOffer ServiceOffer -> Bool
  }

  axioms {
    var T : TradingSystem
    vars S1 S2 : ServiceOffers
    vars N1 N2 N3 : Nodes
    vars E1 E2 : Edges
    vars V1 V2 : ServiceOffer

    eq trading-system-axiom(T)
    =     ((dom-partition((T).partition)) equal-to ((T).offers))
    and ((ran-partition((T).partition)) is-subsumed-by ((T).nodes))
    and ((all-nodes-of ((T).edges)) is-subsumed-by ((T).nodes)) 
    and ((dom-edge-prop((T).edge-properties)) equal-to ((T).edges))  .

    eq service-offer-equality(V1,V2)  =  ((V1).offer-id == (V2).offer-id) .
  }
}


-- 7.4 Static Schema
--

mod* INIT-TRADING-SYSTEM {
  [ InitTradingSystem ]
  extending (TRADING-SYSTEM)
  [ InitTradingSystem < TradingSystem ]

  axioms {
    var T : InitTradingSystem

    eq (T).offers = nil .
    eq (T).nodes  = nil .
    eq (T).partition = empty .
    eq (T).edges = nil .
    eq (T).edge-properties = empty .
  }
}

view TRIV2RETURN from TRIV to RETURN-VALUE {
  sort Elt -> ReturnValue
}

view TRIV2TRADING-SYSTEM from TRIV to TRADING-SYSTEM {
  sort Elt -> TradingSystem
}



mod* BASIC-STATE {
  protecting (2TUPLE[TRIV2RETURN,TRIV2TRADING-SYSTEM]
	      *{ sort 2Tuple -> ValueState })
  signature {
    op new-state : ReturnValue TradingSystem -> ValueState
  }
  axioms {
    var V : ReturnValue
    var S : TradingSystem

    eq new-state(V,S) = <<(V);(S)>> .
  }
}


-- 7.5.1 Export
--

mod* EXPORT-BEHAVIOR {
  protecting (TRADING-SYSTEM)

  signature {
    op value     : TradingSystem ServiceOffer Node -> ServiceOfferIdentifier
    op trans     : TradingSystem ServiceOffer Node -> TradingSystem
    op pre-cond  : TradingSystem ServiceOffer Node -> Bool

    op node-cond : TradingSystem Node -> Bool
    op offer-cond : TradingSystem ServiceOffer -> Bool
    op new-id : ServiceOffers ServiceOfferIdentifier -> Bool
  }

  axioms {
    var S : TradingSystem
    var O : ServiceOffer
    var N : Node
    var X : ServiceOffer
    var L : ServiceOffers
    var I : ServiceOfferIdentifier

    ceq value(S,O,N) = (O).offer-id if pre-cond(S,O,N) .
    ceq value(S,O,N) = void         if not pre-cond(S,O,N) .

    ceq trans(S,O,N)
    = new-trading-system ((add((S).offers,O)),
			  ((S).nodes),
			  (add((S).partition,O,N)),
			  ((S).edges),
			  ((S).edge-properties))   if pre-cond(S,O,N) .
    ceq trans(S,O,N) = S          if not pre-cond(S,O,N) .
    
    eq pre-cond(S,O,N) = (node-cond(S,N)) and (offer-cond(S,O)) .
    eq node-cond(S,N)   = (N) is-member-of ((S).nodes) .
    eq offer-cond(S,O) = new-id ((S).offers, (O).offer-id) .
    
    eq new-id (nil, I)  = true .
    eq new-id ((X L), I)
    = if (((X).offer-id) == I) then false else new-id(L,I) fi .
  }
}


mod* EXPORT {
  protecting (BASIC-STATE)
  protecting (EXPORT-BEHAVIOR)
  signature {
    op export : TradingSystem ServiceOffer Node -> ValueState
  }
  axioms {
    var S : TradingSystem
    var O : ServiceOffer
    var N : Node

    eq export(S,O,N) = new-state(value(S,O,N), trans(S,O,N)) .
  }
}



-- 7.5.2 Withdraw

mod* WITHDRAW-BEHAVIOR {
  protecting (TRADING-SYSTEM)

  signature {
    op value : TradingSystem ServiceOffer -> ReturnValue
    op trans : TradingSystem ServiceOffer -> TradingSystem
    op pre-cond : TradingSystem ServiceOffer -> Bool
  }
  
  axioms {
    var S : TradingSystem
    var O : ServiceOffer

    eq  value(S,O) = void .
    ceq trans(S,O)
    = new-trading-system ((delete((S).offers,O)),
			  ((S).nodes),
			  (delete((S).partition,O)),
			  ((S).edges),
			  ((S).edge-properties))   if pre-cond(S,O) .
    ceq trans(S,O) = S if not pre-cond(S,O) .
    
    eq pre-cond(S,O) = (O) is-member-of ((S).offers) .
  }
}

mod* WITHDRAW {
  protecting (BASIC-STATE)
  protecting (WITHDRAW-BEHAVIOR)
  signature {
    op withdraw : TradingSystem ServiceOffer  -> ValueState
  }
  axioms {
    var S : TradingSystem
    var O : ServiceOffer

    eq withdraw(S,O) = new-state(value(S,O), trans(S,O)) .
  }
}


-- 7.5.3 Modify Offer (1997.7.7)

-- SERVICE-OFFER in iv-2.obj


mod* PROPERTY-VALUES-LIBRARY {
  protecting (THE-PROPERTY-VALUES)

  signature {
    op dom-property  : PropertyValues -> Names
    op dom-prop-exec : PropertyValues Names -> Names

    op delete-s   : PropertyValues Names -> PropertyValues
    op del-s-exec : PropertyValues Names -> PropertyValues
    op override-s : PropertyValues PropertyValues -> PropertyValues
    op over-s-exec  : PropertyValues PropertyValues -> PropertyValues
  }

  axioms {
    var V : Property
    vars P P1 P2 : PropertyValues
    var N : Name 
    var L : Names

    eq dom-property(P) = dom-prop-exec(P,nil) .
    eq dom-prop-exec(empty,L) = rev(L) .
    eq dom-prop-exec((V P),L) = dom-prop-exec(P,((1*(V)) L)) .

    eq delete-s(P,L) = del-s-exec(P,L) .
    eq del-s-exec(P,nil) = P .
    eq del-s-exec(P,(N L)) = del-s-exec(delete(P,N),L) .

    eq override-s(P1,P2) = over-s-exec(P1,P2) .
    eq over-s-exec(P1,empty) = P1 .
    eq over-s-exec(P1,(V P2)) = over-s-exec(override(P1,(1*(V)),(2*(V))),P2) .
  }
}


mod* SERVICE-OFFER-LIBRARY {
  protecting (TRADING-SYSTEM-AXIOMS)

  signature {
    op is-member-offer-of : ServiceOffer ServiceOffers -> Bool
    op find-matched-offer : ServiceOffer ServiceOffers -> ServiceOffer
    op override-offer : ServiceOffer ServiceOffers -> ServiceOffers
    op override-offer-of-partition : ServiceOffer Partitions -> Partitions
    op oo-exec : ServiceOffer ServiceOffers ServiceOffers -> ServiceOffers
    op op-exec : ServiceOffer Partitions Partitions -> Partitions
  }

  axioms {
    vars S S1 S2 : ServiceOffer
    vars O O2 : ServiceOffers
    vars P P2 : Partitions
    var T2 : Partition

    eq is-member-offer-of(S1,nil) = false .
    eq is-member-offer-of(S1,(S2 O))
    =  if service-offer-equality(S1,S2) then true
      else is-member-offer-of(S1,O) fi .

    eq find-matched-offer(S1,(S2 O))
    =  if service-offer-equality(S1,S2) then S2
      else find-matched-offer(S1,O) fi .

    eq override-offer(S,O) = oo-exec(S,O,nil) .
    eq oo-exec(S1,(S2 O2),O)
    =  if service-offer-equality(S1,S2) then (rev(O) (S1 O2))
    else oo-exec(S1,O2,(S2 O)) fi .

    eq override-offer-of-partition(S,P) = op-exec(S,P,empty) .
    eq op-exec(S1,(T2 P2),P)
    =  if service-offer-equality(S1,(1*(T2)))
    then (rev(P) (({(S1),(2*(T2))}) P2))
    else op-exec(S1,P2,(T2 P)) fi .
  }
}


mod* MODIFY-SERVICE-OFFER {
  protecting (SERVICE-OFFER)
  protecting (PROPERTY-VALUES-LIBRARY)
  protecting (THE-SERVICE-TYPE-PROPERTIES)

  signature {
    op modify-service-offer : 
      ServiceOffer Names PropertyValues PropertyValues -> ServiceOffer
    op is-modifiable : ServiceOffer Names PropertyValues PropertyValues -> Bool
    op modify-property :
      PropertyValues Names PropertyValues PropertyValues -> PropertyValues
  }

  axioms {
    var S : ServiceOffer
    var N : Names
    vars P P1 P2 : PropertyValues

    eq modify-service-offer(S,N,P1,P2)
    =  new-service-offer(((S).service-type),
			 (modify-property((S).prop-vals,N,P1,P2)),
			 ((S).interface-id),
			 ((S).offer-id)) .

    eq modify-property(P,N,P1,P2) = (override-s(delete-s(P,N),P2)) cup (P1) .

    eq is-modifiable(S,N,P1,P2)
    =   is-empty((N) cap (mandatory-props((S).service-type)))
    and is-empty((N) cap (readonly-props((S).service-type)))
    and ((N) cup (dom-property(P2))) is-subsumed-by (dom-property((S).prop-vals))
    and is-empty((dom-property(P1)) cap (dom-property((S).prop-vals))) .
  }
}


mod* MODIFY-OFFER-BEHAVIOR {
  protecting (TRADING-SYSTEM)
  protecting (MODIFY-SERVICE-OFFER)
  protecting (SERVICE-OFFER-LIBRARY)

  signature {
    op value     :
      TradingSystem ServiceOffer Names PropertyValues PropertyValues
	-> ReturnValue
    op trans     :
      TradingSystem ServiceOffer Names PropertyValues PropertyValues
	-> TradingSystem
    op pre-cond  :
      TradingSystem ServiceOffer Names PropertyValues PropertyValues -> Bool
    op modified-trading-system :
      TradingSystem ServiceOffer -> TradingSystem
    op trans-body :
      TradingSystem ServiceOffer Names PropertyValues PropertyValues
	-> TradingSystem
  }
  
  axioms {
    var S : TradingSystem
    var O : ServiceOffer
    var N : Names 
    vars P P1 P2 : PropertyValues
      
    eq value(S,O,N,P1,P2) = void .

    ceq trans(S,O,N,P1,P2) = trans-body(S,O,N,P1,P2)  if pre-cond(S,O,N,P1,P2) .
    ceq trans(S,O,N,P1,P2) = S if not(pre-cond(S,O,N,P1,P2)) .

    eq trans-body(S,O,N,P1,P2)
    = if is-modifiable(O,N,P1,P2)
    then modified-trading-system(S,
				 modify-service-offer(find-matched-offer(O,((S).offers)),N,P1,P2))
    else S fi   .

    eq modified-trading-system(S,O)
    = new-trading-system((override-offer(O, ((S).offers))),
			 ((S).nodes),
			 (override-offer-of-partition(O, ((S).partition))),
			 ((S).edges),
			 ((S).edge-properties)) .

    eq pre-cond(S,O,N,P1,P2) = is-member-offer-of (O,(S).offers) .
  }
}


mod* MODIFY-OFFER {
  protecting (BASIC-STATE)
  protecting (MODIFY-OFFER-BEHAVIOR)

  signature {
    op modify-offer :
      TradingSystem ServiceOffer Names PropertyValues PropertyValues -> ValueState
  }

  axioms {
    var S : TradingSystem
    var O : ServiceOffer
    var N : Names
    vars P1 P2 : PropertyValues

    eq modify-offer(S,O,N,P1,P2)
    =  new-state(value(S,O,N,P1,P2), trans(S,O,N,P1,P2)) .
  }
}




-- 7.5.4 Add Edge


mod* ADD-EDGE-BEHAVIOR {
  protecting (TRADING-SYSTEM)

  signature {
    op value     : TradingSystem Node Node PropertyValues -> ReturnValue
    op trans     : TradingSystem Node Node PropertyValues -> TradingSystem
    op pre-cond  : TradingSystem Node Node PropertyValues -> Bool
  }

  axioms {
    var S : TradingSystem
    vars N1 N2 : Node
    var P : PropertyValues

    eq value(S,N1,N2,P) = void .

    ceq trans(S,N1,N2,P)
    = new-trading-system(((S).offers),
			 ((S).nodes),
			 ((S).partition),
			 (add((S).edges, edge(N1,N2))),
			 (add((S).edge-properties, edge(N1,N2), P)))
    if pre-cond(S,N1,N2,P) .
    ceq trans(S,N1,N2,P) = S if not(pre-cond(S,N1,N2,P)) .
    
    eq pre-cond(S,N1,N2,P) = ((N1) is-member-of ((S).nodes))
    and ((N2) is-member-of ((S).nodes))
    and not((edge(N1,N2)) is-member-of ((S).edges)) .
  }
}

mod* ADD-EDGE {
  protecting (BASIC-STATE)
  protecting (ADD-EDGE-BEHAVIOR)
  signature {
    op add-edge : TradingSystem Node Node PropertyValues  -> ValueState
  }
  axioms {
    var S : TradingSystem
    vars N1 N2 : Node
    var P : PropertyValues

    eq add-edge(S,N1,N2,P) = new-state(value(S,N1,N2,P), trans(S,N1,N2,P)) .
  }
}


-- 7.5.5 Remove Edge


mod* REMOVE-EDGE-BEHAVIOR {
  protecting (TRADING-SYSTEM)

  signature {
    op value     : TradingSystem Edge -> ReturnValue
    op trans     : TradingSystem Edge -> TradingSystem
    op pre-cond  : TradingSystem Edge -> Bool
  }

  axioms {
    var S : TradingSystem
    var E : Edge

    eq value(S,E) = void .

    ceq trans(S,E)
    = new-trading-system(((S).offers),
			 ((S).nodes),
			 ((S).partition),
			 (delete((S).edges, E)),
			 (delete((S).edge-properties, E))) 
    if pre-cond(S,E) .

    ceq trans(S,E) = S if not(pre-cond(S,E)) .
    eq pre-cond(S,E) = (E) is-member-of ((S).edges) .
  }
}

mod* REMOVE-EDGE {
  protecting (BASIC-STATE)
  protecting (REMOVE-EDGE-BEHAVIOR)
  signature {
    op remove-edge : TradingSystem Edge  -> ValueState
  }
  axioms {
    var S : TradingSystem
    var E : Edge

    eq remove-edge(S,E) = new-state(value(S,E), trans(S,E)) .
  }
}


-- 7.5.6 Modify Edge


mod* MODIFY-EDGE-BEHAVIOR {
  protecting (TRADING-SYSTEM)

  signature {
    op value     : TradingSystem Edge PropertyValues -> ReturnValue
    op trans     : TradingSystem Edge PropertyValues -> TradingSystem
    op pre-cond  : TradingSystem Edge PropertyValues -> Bool
  }

  axioms {
    var S : TradingSystem 
    var E : Edge
    var P : PropertyValues

    eq value(S,E,P) = void .

    ceq trans(S,E,P)
    = new-trading-system(((S).offers),
			 ((S).nodes),
			 ((S).partition),
			 ((S).edges),
			 (override((S).edge-properties, E, P))) 
    if pre-cond(S,E,P) .

    ceq trans(S,E,P) = S if not(pre-cond(S,E,P)) .
    eq pre-cond(S,E,P) = (E) is-member-of ((S).edges) .
  }
}

mod* MODIFY-EDGE {
  protecting (BASIC-STATE)
  protecting (MODIFY-EDGE-BEHAVIOR)

  signature {
    op modify-edge : TradingSystem Edge PropertyValues -> ValueState
  }
  axioms {
    var S : TradingSystem
    var E : Edge
    var P : PropertyValues

    eq modify-edge(S,E,P) = new-state(value(S,E,P), trans(S,E,P)) .
  }
}


-- 7.5.7 Add Node


mod* ADD-NODE-BEHAVIOR {
  protecting (TRADING-SYSTEM)

  signature {
    op value     : TradingSystem Node -> ReturnValue
    op trans     : TradingSystem Node -> TradingSystem
    op pre-cond  : TradingSystem Node -> Bool
  }

  axioms {
    var S : TradingSystem
    var N : Node

    eq value(S,N) = void .

    ceq trans(S,N)
    = new-trading-system(((S).offers),
			 (add(((S).nodes),N)),
			 ((S).partition),
			 ((S).edges),
			 ((S).edge-properties))
    if pre-cond(S,N) .

    ceq trans(S,N) = S if not(pre-cond(S,N)) .
    eq pre-cond(S,N) = (N) is-member-of ((S).nodes) .
  }
}

mod* ADD-NODE {
  protecting (BASIC-STATE)
  protecting (ADD-NODE-BEHAVIOR)
  signature {
    op add-node : TradingSystem Node  -> ValueState
  }
  axioms {
    var S : TradingSystem
    var N : Node

    eq add-node(S,N) = new-state(value(S,N), trans(S,N)) .
  }
}


-- 7.5.8 Remove Node


mod* REMOVE-NODE-BEHAVIOR {
  protecting (TRADING-SYSTEM)
  protecting (TRADING-SYSTEM-LIBRARY)

  signature {
    op value     : TradingSystem Node -> ReturnValue
    op trans     : TradingSystem Node -> TradingSystem
    op pre-cond  : TradingSystem Node -> Bool
  }

  axioms {
    var S : TradingSystem
    var N : Node

    eq value(S,N) = void .

    ceq trans(S,N)
    = new-trading-system(((S).offers),
			 (delete(((S).nodes),N)),
			 ((S).partition),
			 ((S).edges),
			 ((S).edge-properties))
    if pre-cond(S,N) .

    ceq trans(S,N) = S if not(pre-cond(S,N)) .
    eq pre-cond(S,N) = ((N) is-member-of ((S).nodes))
    and (not ((N) is-member-of (ran-partition((S).partition))))
    and (not ((N) is-member-of (all-nodes-of((S).edges)))) .
  }
}

mod* REMOVE-NODE {
  protecting (BASIC-STATE)
  protecting (REMOVE-NODE-BEHAVIOR)
  signature {
    op remove-node : TradingSystem Node  -> ValueState
  }
  axioms {
    var S : TradingSystem
    var N : Node

    eq remove-node(S,N) = new-state(value(S,N), trans(S,N)) .
  }
}

! date

--
eof
