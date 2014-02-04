** ==========================================
** Experimental Metalevel features of CafeOBJ
** ==========================================

-- =====================================
-- CHAOS:OBJECT: Everything in METALEVEL
-- =====================================

module CHAOS:OBJECT {
  imports {
    protecting(CHAOS:META)
    protecting(ID)
    protecting(TRUTH-VALUE)
    protecting(STRING)
    protecting(INT-VALUE)
  }
  signature {
    [ Int *Sort* *Operator* *Term* *Axiom*
      *Signagure* *Trs* *ChaosPair* *AxiomSet* *Module* *Substitution* *Import*
      < *CafeObject* ]
    [ String < *ModExpr* < *CafeObject* ]
    [ String < *Label* < *CafeObject* ]
    -- op :nil         : -> *Cosmos*
    -- op (_,_)        : *Cosmos* *Cosmos* -> *Cosmos* {assoc id: :nil}
    -- op ([:obj_])    : *Cosmos* -> *CafeObject*
    -- op ([::_])      : *Cosmos* -> *CafeList*
    op :!           : String *Cosmos* -> *Cosmos*
    op :!!          : String *Cosmos* -> *Cosmos*
    op (:str)      : *Cosmos* -> String
  }
  axioms {
    eq :!!(S:String, X:*Cosmos*) = #!! (do-apply!! S X) .
    eq :!(S:String, X:*Cosmos*) = #! (do-apply! S X) .
    -- eq [:obj X:*Cosmos*] = :!!("CREATE-SYSTEM-OBJECT-TERM", (X)) .
    -- eq [:: X:*Cosmos*] = :!!("CREATE-CHAOS-LIST", X) .
    eq :str(X:*CafeObject*) =
      #!! (funcall #'(lambda (y) (make-bconst-term *string-sort*
				    (with-output-to-string (str)
				     (print-chaos-object (meta-term-term y) str) str))) X) .
   }
}

**
** CHAOS:LIST: List of *CafeObject*
** 
module CHAOS:LIST {
  imports {
    protecting(CHAOS:OBJECT)
  }
  signature {
    [ *CafeObject* < *CafeList* ]
    op (:[])      : -> *CafeList* {constr}
    op (:[_,_])   : *CafeList* *CafeList* -> *CafeList* {constr assoc id: (:[])}
    -- op _,_        : *CafeList* *CafeList* -> *CafeList* {constr assoc id: (:[])}
    op (:nth)     : Nat *CafeList* -> *CafeObject*
    op (:rest)    : *CafeList* -> *CafeList*
    op (:nthrest) : Nat *CafeList* -> *CafeList*
    op (:append)  : *CafeList* *CafeList* -> *CafeList*
    op (:length)  : *CafeList* -> Nat
  }
  axioms {
    -- eq :[] = #!! (create-system-object-term *chaos-null*) .
    -- eq :[X:*CafeObject*, Y:*CafeList*] =
    --  #!! (create-system-object-term
    --	     (make-chaos-list :list (cons (term-system-object X)
    --				          (chaos-list-list (term-system-object Y))))) .
    eq :append(X:*CafeList*, Y:*CafeList*) =
      #!! (create-system-object-term
	     (make-chaos-list :list (append (term-system-object X)
				            (term-system-object Y)))) .
    eq :nth(N:Nat, L:*CafeList*) =
      #!! (create-system-object-term (mnth (term-system-object L) (term-builtin-value N))) .
    eq :rest(L:*CafeList*) = :nthrest(1, L) .
    eq :nthrest(N:Nat, L:*CafeList*) =
      #!! (create-system-object-term (mnthcdr (term-system-object L) (term-builtin-value N))) .
    eq :length(L:*CafeList*) = #! (mlength (term-system-object L)) .
  }
}

**
** CHAOS:MODULE: CafeOBJ Module
** M   = (Sig, E) 
** 
module CHAOS:MODULE {
  imports {
    protecting(CHAOS:LIST)
  }
  signature {
    [ *InitialModule* *FinalModule* *LooseModule* < *Module* ]
    op (:mod![_])      : *ModExpr* -> *InitialModule*
    op (:mod*[_])      : *ModExpr* -> *FinalModule*
    op (:mod[_])       : *ModExpr* -> *LooseModule*
    op (:sig[_])       : *Module* -> *Signature*
    op (:sig[_:all])   : *Module* -> *Signature*
    op (:axset[_])     : *Module* -> *AxiomSet*
    op (:axset[_:all]) : *Module* -> *AxiomSet*
    op (:sorts)        : *Signature* -> *CafeList*
    op (:psort)        : *Signature* -> *Sort*
    op (:ops)          : *Signature* -> *CafeList*
    op (:eqs)          : *AxiomSet* -> *CafeList*
    op (:trans)        : *AxiomSet* -> *CafeList*
    op (:vars)         : *AxiomSet* -> *CafeList*
  }
  axioms {
    eq :mod![S:String] =
      #!! (create-system-object-term (eval-modexp (parse-modexp (term-builtin-value S)))) .
    eq :mod*[S:String] =
      #!! (create-system-object-term (eval-modexp (parse-modexp (term-builtin-value S)))) .
    eq :mod[S:String] =
      #!! (create-system-object-term (eval-modexp (parse-modexp (term-builtin-value S)))) .
    eq :sig[M:*Module*] =
      #!! (create-system-object-term (module-signature (term-system-object M))) .
    eq :sig[M:*Module* :all]
    = #!! (create-system-object-term (module-all-signature (term-system-object M))) .
    eq :axset[M:*Module*] =
      #!! (create-system-object-term (module-axiom-set (term-system-object M))) .
    eq :axset[M:*Module* :all ] =
      #!! (create-system-object-term (module-axiom-set-all (term-system-object M))) .
    eq :sorts(X:*Signature*) = #!! (create-list-of-objects #'signature$sorts X) .
    eq :ops(X:*Signature*) = #!! (create-list-of-objects #'signature-methods X) .
    eq :eqs(A:*AxiomSet*) = #!! (create-list-of-objects #'axiom-set$equations A) .
    eq :trans(A:*AxiomSet*) = #!! (create-list-of-objects #'axiom-set$rules A) .
    eq :vars(A:*AxiomSet*) = #!! (create-list-of-objects #'axiom-set$variables A) .
  }
}

module CHAOS:SORT {
  imports {
    protecting(CHAOS:MODULE)
  }
  signature {
    [ *Sort* < *SortList* ]
    op 'nil : -> *SortList* {constr}
    op __ : *SortList* *SortList* -> *SortList* { assoc id: 'nil }
    op (:sort[_])     : String -> *Sort*
    op (:sort[_in_])  : String *Module* -> *Sort*
    pred (_:s<_)      : *Sort* *Sort*
    pred (_:s=_)      : *Sort* *Sort*
    pred (_:s<=_)      : *Sort* *Sort*
    pred (_:same-cc_) : *Sort* *Sort*
  }
  axioms {
    eq :sort[S:String] = #!! (create-system-object-term (find-qual-sort (term-builtin-value S))) .
    eq :sort[S:String in M:*Module*] =
      #!! (create-system-object-term
	     (find-sort-in (term-system-object M))) .
    eq S1:*Sort* :s< S2:*Sort* =
      #!! (coerce-to-bool (sort-compare '< (term-system-object S1) (term-system-object S2))) .
    eq S1:*Sort* :s= S2:*Sort* =
      #!! (coerce-to-bool (eq (term-system-object S1) (term-system-object S2))) .
    eq S1:*Sort* :s<= S2:*Sort* = (S1 :s< S2) or (S1 :s= S2) .
    eq S1:*Sort* :same-cc S2:*Sort* =
      #!! (coerce-to-bool (in-same-cc (term-system-object S1) (term-system-object S2))) .
  }
}

module CHAOS:OPERATOR {
  imports {
    protecting(CHAOS:SORT)
  }
  signature {
    op (:op[_:_->_]) : String *SortList* *Sort* -> *Operator*
    op (:arity)      : *Operator* -> *CafeList*
    op (:coarity)    : *Operator* -> *Sort*
    op (:prec)       : *Operator* -> Nat
    op (:strat)      : *Operator* -> *CafeList*
    op (:theory)     : *Operator* -> *OpTheory*
  }
  axioms {
    eq :arity(O:*Operator*) =
      #!! (create-list-of-objects #'(lambda (x) (method-arity x)) O) .
    eq :coarity(O:*Operator*) =
      #!! (create-system-object-term (method-coarity (term-system-object O))) .
    eq :prec(O:*Operator*) = #! (method-precedence (term-system-object O)) .
    eq :strat(O:*Operator*) = #!! (create-system-object-term
				       (make-chaos-list :list (method-rewrite-strategy (term-system-object O)))) .
    eq :op[Name:String : Arity:*SortList* -> Coarity:*Sort* ] =
      #!! (create-system-object-term
	     (find-method-in *current-module* (read-opname-from-string (term-builtin-value Name))
	                                      (mapcar #'(lambda (x) (term-system-object x))
                                                      (list-assoc-subterms Arity (term-head Arity)))
                                              (term-system-object Coarity))) .
  }
}
  
module CHAOS:TERM {
  imports {
    protecting(CHAOS:OPERATOR)
    -- protecting(RWL)
  }
  signature {
    [ Nat < *NatLst* < *Occurence* < *CafeObject* ]
    op '[ _ ]             : *Cosmos* -> *Term* { strat: (0) constr }
    op (:term)            : *Term* -> *Cosmos* { strat: (0) }
    op (:subst-image)     : *Term* *Substitution* -> *Term*
    op (:match_:with_)    : *Term* *Term* -> *Substitution*
    op nil                : -> *NatLst* { constr }
    op _,_                : *NatLst* *NatLst* -> *NatLst* { assoc id: nil constr }
    op [_]                : *NatLst* -> *Occurence* { constr }
    pred (:is-var?)       : *Term*
    pred (:is-appl?)      : *Term*
    pred (:is-bconst?)    : *Term*
    pred (:is-pconst?)    : *Term*
    pred (:is-sysobj?)    : *Term*
    pred _==_             : *Term* *Term*
    pred _=_              : *Term* *Term*
    op (:op)              : *Term* -> *Operator* 
    op (:sort-of)         : *Term* -> *Sort*
    op (:subterm)         : Nat *Term* -> *Term*
    op (:subterms)        : *Term* -> *CafeList*
    op bsubterms          : *Term* -> *CafeList*
    op (:parse)           : String -> *Term*
    op (:reduce)          : *Term* -> *Cosmos*
    op (:reduce)          : String -> *Cosmos*
    op (:reduce :in_:_)   : *Module* String -> *Cosmos* {strat: (1 0)}
    op (:parse :in_:_)    : *Module* String -> *Cosmos*
  }
  axioms {
    eq :term(T1:*Term*) = #!! (meta-term-term T1) .
    eq :match T1:*Term* :with T2:*Term* =
      #!! (create-system-object-term
	     (do-meta-match (meta-term-term T1)
	      (meta-term-term T2))) .
    eq :subst-image(T1:*Term*, S:*Substitution*) =
      #!! (meta-subst-image (meta-term-term T1)
	   (term-system-object S)) .
    eq :is-var?(T1:*Term*) = #!! (coerce-to-bool (term-is-variable? (meta-term-term T1))) .
    eq :is-appl?(T1:*Term*) = #!! (coerce-to-bool (term-is-applform? (meta-term-term T1))) .
    eq :is-bconst?(T1:*Term*) = #!! (coerce-to-bool (term-is-builtin-constant? (meta-term-term T1))) .
    eq :is-pconst?(T1:*Term*) = #!! (coerce-to-bool (term-is-psuedo-constant? (meta-term-term T1))) .
    eq :is-sysobj?(T1:*Term*) = #!! (coerce-to-bool (term-is-system-object? (meta-term-term T1))) .
    eq T1:*Term* ==  T2:*Term* = :term(T1) == :term(T2) .
    eq (T1:*Term* = T2:*Term*) = (:term(T1) = :term(T2)) .
    eq :op(T1:*Term*) = #!! (create-system-object-term (term-head (meta-term-term T1))) .
    eq :sort-of(T1:*Term*) = #!! (create-system-object-term (term-sort (meta-term-term T1))) .
    eq :subterm(X:Nat, T1:*Term*) =
      #!! (make-meta-term (term-arg-n (meta-term-term T1) (term-builtin-value X))) .
    eq :subterms(T1:*Term*) = :[bsubterms(T1),:[]] .
    eq bsubterms(T1:*Term*)  =  #!!(mapcar #'(lambda (x) (make-meta-term x))
				    (term-subterms (meta-term-term T1))) .
    eq :parse(S:String) =
      #!! (create-system-object-term (simple-parse-from-string(term-builtin-value S))) .
    -- eq subterm(T1:*Term*, Oc:*Occurence*) = #!! (meta-occur-at T1 Oc) .
    eq :reduce(T1:*Term*) = :term(T1) .
    eq (:reduce :in M:*Module* : T1:String) =
      #!! (perform-meta-reduction (term-builtin-value T1) (term-system-object M) :red) .
  }
}

**
** AXIOM: Todo
**
module CHAOS:AXIOM {
  imports {
    protecting(CHAOS:TERM)
  }
  signature {
    [ *Eq* *CEq* *Beq* *CBeq* *Tr* *CTr* < *Axiom* ]
    op (:lhs)            : *Axiom* -> *Term*
    op (:rhs)            : *Axiom* -> *Term*
    op (:cond)           : *Axiom* -> *Term*
    op (:labels)         : *Axiom* -> *CafeList*
    op :ax[_]            : *Label* -> *Axiom*
    op :ax[_in_]         : *Label* *Module* -> *Axiom*
    op :eq[_=_]          : *Term* *Term* -> *Eq*
    op :ceq[_=_:if_]     : *Term* *Term* *Term* -> *CEq*
    op :beq[_=_]         : *Term* *Term* -> *Beq*
    op :cbeq[_=_:if_]    : *Term* *Term* *Term* -> *CBeq*
    op :trans[_=>_]      : *Term* *Term* -> *Tr*
    op :ctrans[_=>_:if_] : *Term* *Term* *Term* -> *CTr*
  }
  axioms {
    -- eq [:axiom S:String] = 
  }
}

module METALEVEL {
  imports {
    protecting(CHAOS:AXIOM)
  }
  signature {
    op (:eval)         : String -> *CafeObject*
    -- op (:apply_to_)    : *AxiomSpec* *Term* -> *Cosmos*
    -- op (:apply_to_at_) : *AxiomSpec* *Term* *Occurence* -> *Cosmos*
  }
  axioms {
    eq :eval(X:String) =
      #!! (create-system-object-term (parse-cafeobj-input-from-string (term-builtin-value X))) .
    -- eq :apply A:*AxiomSpec* to T1:*Term* = rep("apply " ++ A ++ "to" ++ :str[(term(T1))]) .
  }
}

evq 
(let ((meta-mod (eval-modexp "METALEVEL")))
  (with-in-module (meta-mod)
    (let* ((term-op (find-operator '("'" "[" "_" "]") 1 *current-module*))
	   (term-meth (lowest-method* (car (opinfo-methods term-op)))))
       (setq *op-term* term-meth))))

provide meta
eof
--

