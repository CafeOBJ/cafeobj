**
** CHAOS:OBJECT: Everything in METALEVEL
**

module CHAOS:OBJECT {
  imports {
    protecting(CHAOS:META)
    protecting(TRUTH-VALUE)
    protecting(STRING)
    protecting(INT-VALUE)
  }
  signature {
    [ *Void* < Int String *Sort* *Operator* *Term* *Axiom* *ChaosList* *ChaosExpr*
      *Signagure* *Trs* *Label* *ChaosPair* *AxiomSet* *Module* *Substitution* *Imports*
      < *ChaosObject* ]
    [ String < *ModExpr* ]
    [ String < *Label* ]
    op :nil         : -> *Cosmos*
    op (_,_)        : *Cosmos* *Cosmos* -> *Cosmos* {assoc id: :nil}
    op ([:obj_])    : *Cosmos* -> *ChaosObject*
    op ([::_])      : *Cosmos* -> *ChaosList*
    op :!           : String *Cosmos* -> *Cosmos*
    op :!!          : String *Cosmos* -> *Cosmos*
    op ([:str_])      : *Cosmos* -> String
  }
  axioms {
    eq :!!(S:String, X:*Cosmos*) = #!! (do-apply!! S X) .
    eq :!(S:String, X:*Cosmos*) = #! (do-apply! S X) .
    eq [:obj X:*Cosmos*] = :!!("CREATE-SYSTEM-OBJECT-TERM", (X)) .
    eq [:: X:*Cosmos*] = :!!("CREATE-CHAOS-LIST", X) .
    eq [:str X:*Cosmos* ] = #!! (funcall #'(lambda (y) (make-bconst-term *string-sort*
							  (with-output-to-string (str) (print-chaos-object (meta-term-term y) str) str))) X) .
   }
}

**
** CHAOS:LIST: List of *ChaosObject*
** 
module CHAOS:LIST {
  imports {
    protecting(CHAOS:OBJECT)
  }
  signature {
    op 'nil    : -> *ChaosList*
    op nth     : Nat *ChaosList* -> *ChaosObject*
    op rest    : *ChaosList* -> *ChaosList*
    op nthrest : Nat *ChaosList* -> *ChaosList*
    op cons    : *ChaosObject* *ChaosList* -> *ChaosList*
    op append  : *ChaosList* *ChaosList* -> *ChaosList*
  }
  axioms {
    eq 'nil = #!! (create-system-object-term *chaos-null*) .
    eq cons(X:*ChaosObject*, Y:*ChaosList*) 
    = #!! (create-system-object-term
	     (make-chaos-list :list (cons (term-system-object X)
 				          (chaos-list-list (term-system-object Y))))) .
    eq append(X:*ChaosList*, Y:*ChaosList*)
    = #!! (create-system-object-term
	     (make-chaos-list :list (append (term-system-object X)
				            (term-system-object Y)))) .
    eq nth(N:Nat, L:*ChaosList*)
    = #!! (create-system-object-term (mnth (term-system-object L) (term-builtin-value N))) .
    eq rest(L:*ChaosList*) = nthrest(1, L) .
    eq nthrest(N:Nat, L:*ChaosList*) 
    = #!! (create-system-object-term (mnthcdr (term-system-object L) (term-builtin-value N))) .
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
    op [:module_]     : *ModExpr* -> *Module*
    op [:signature_]  : String -> *Signature*
    op [:signature_]  : *Module* -> *Signature*
    op [:axiomset_]   : String -> *AxiomSet*
    op [:axiomset_]   : *Module* -> *AxiomSet*
    op [:trs_]        : String -> *Trs*
    op [:trs_]        : *Module* -> *Trs*
    op sorts          : *Signature* -> *ChaosList*
    op principal-sort : *Signature* -> *Sort*
    op operators      : *Signature* -> *ChaosList*
    op axioms         : *AxiomSet* -> *ChaosList*
    op variables      : *AxiomSet* -> *ChaosList*
    op rules          : *AxiomSet* -> *ChaosList*
  }
  axioms {
    eq [:module S:String] = #!! (create-system-object-term (eval-modexp (parse-modexp (term-builtin-value S)))) .
    eq [:signature S:String] = #!! (create-system-object-term
				       (module-signature (eval-modexp (parse-modexp (term-builtin-value S))))) .
    eq [:signature M:*Module*] = #!! (create-system-object-term (module-signature (term-system-object M))) .
    eq [:axiomset S:String] = #!! (create-system-object-term
				       (module-axiom-set (eval-modexp (parse-modexp (term-builtin-value S))))) .
    eq [:axiomset M:*Module*] = #!! (create-system-object-term (module-axiom-set (term-system-object M))) .
    eq [:trs S:String] = #!! (create-system-object-term
				       (module-trs (eval-modexp (parse-modexp (term-builtin-value S))))) .
    eq [:trs M:*Module*] = #!! (create-system-object-term (module-trs (term-system-object M))) .
    eq sorts(X:*Signature*) = #!! (create-list-of-objects #'signature$sorts X) .
    eq operators(X:*Signature*) = #!! (create-list-of-objects #'signature-methods X) .
    eq axioms(A:*AxiomSet*) = #!! (create-list-of-objects #'axiom-set$equations A) .
    eq variables(A:*AxiomSet*) = #!! (create-list-of-objects #'axiom-set$variables A) .
    eq rules(A:*AxiomSet*) = #!! (create-list-of-objects #'axiom-set$rules A) .
  }
}

module CHAOS:SORT {
  imports {
    protecting(CHAOS:MODULE)
  }
  signature {
    [ *Sort* < *SortList* < *ChaosList* ]
    op __ : *SortList* *SortList* -> *SortList* { assoc id: 'nil }
    op [:sort_] : String -> *Sort*
    op [:sort__] : String String -> *Sort*
    pred _<_ : *Sort* *Sort*
    pred _s=_ : *Sort* *Sort*
    pred _<=_ : *Sort* *Sort*
    pred _in-same-cc_ : *Sort* *Sort*
  }
  axioms {
    eq [:sort S:String] = #!! (create-system-object-term (find-qual-sort (term-builtin-value S))) .
    eq [:sort S:String M:String] = #!! (create-system-object-term
                                          (find-sort-in (eval-modexp (parse-modexp (term-builtin-value M)))
					                (term-builtin-value S))) .
    eq S1:*Sort* < S2:*Sort* = #!! (coerce-to-bool (sort-compare '< (term-system-object S1) (term-system-object S2))) .
    eq S1:*Sort* s= S2:*Sort* = #!! (coerce-to-bool (eq (term-system-object S1) (term-system-object S2))) .
    eq S1:*Sort* <= S2:*Sort* = (S1 < S2) or (S1 s= S2) .
    eq S1:*Sort* in-same-cc S2:*Sort* = #!! (coerce-to-bool (in-same-cc (term-system-object S1) (term-system-object S2))) .
  }
}

module CHAOS:OPERATOR {
  imports {
    protecting(CHAOS:SORT)
  }
  signature {
    op ([:operator_:_->_]) : String *SortList* *Sort* -> *Operator*
    op arity   : *Operator* -> *ChaosList*
    op coarity : *Operator* -> *Sort*
    op precedence : *Operator* -> Nat
    op strategy : *Operator* -> *ChaosList*
    -- op theory : *Operator* -> *EquationalTheory*
  }
  axioms {
    eq arity(O:*Operator*) = #!! (create-list-of-objects #'(lambda (x) (method-arity x)) O) .
    eq coarity(O:*Operator*) = #!! (create-system-object-term (method-coarity (term-system-object O))) .
    eq precedence(O:*Operator*) = #! (method-precedence (term-system-object O)) .
    eq strategy(O:*Operator*) = #!! (create-system-object-term
				       (make-chaos-list :list (method-strategy (term-system-object O)))) .
    eq [:operator Name:String : Arity:*SortList* -> Coarity:*Sort* ]
    = #!! (create-system-object-term
	     (find-method-in *current-module* (read-opname-from-string (term-builtin-value Name))
	                                      (mapcar #'(lambda (x) (term-system-object x))
                                                      (list-assoc-subterms Arity (term-head Arity)))
                                              (term-system-object Coarity))) .
  }
}
  

module CHAOS:TERM {
  imports {
    protecting(CHAOS:OPERATOR)
    protecting(RWL)
  }
  signature {
    op '[ _ ] : *Cosmos* -> *Term* { strat: (0) }
    op term : *Term* -> *Cosmos* {strat: (0)}
    op subst-image : *Term* *Substitution* -> *Term*
    op match_with_ : *Term* *Term* -> *ChaosList*
    op axioms : *Term* -> *ChaosList*
    op [] : -> *Occurence* { constr }
    op [_,_] : Nat *Occurence* -> *Occurence* {assoc :id [] constr}
    pred is-variable : *Term*
    pred is-application-form : *Term*
    pred is-builtin-constant : *Term*
    pred is-p-constant : *Term*
    pred is-system-object : *Term*
    pred _==_ : *Term* *Term*
    pred _=_ : *Term* *Term*
    op _=>_ : *Term* *Term* -> *ChaosList*
    op operator : *Term* -> *Operator* 
    op sort-of : *Term* -> *Sort*
    op subterm : Nat *Term* -> *Term*
    op subterms : *Term* -> *ChaosList*
    op subterm : *Term* *Occurence* -> *Term*
    op parse : String -> *Term*
    op reduce : *Term* -> *Cosmos*
    -- op reduce : String -> *Cosmos*
    op (reduce in_:_) : *Module* String -> *Cosmos* {strat: (1 0)}
    op (parse in_:_) : *Module* String -> *Cosmos*
    op (:BOOL) : *Term* -> Bool
  }
  axioms {
    eq term(T1:*Term*) = #!! (meta-term-term T1) .
    eq match T1:*Term* with T2:*Term* = #!! (create-system-object-term
					       (do-meta-match (meta-term-term T1)
						              (meta-term-term T2))) .
    eq subst-image(T1:*Term*, S:*Substitution*) = #!! (meta-subst-image (meta-term-term T1)
						                        (term-system-object S)) .
    eq (:BOOL(T1:*Term*)) = term(T1) .
    ** eq axioms(T1:*Term*) = !! 
    eq T1:*Term* => T2:*Term* = #!! (create-system-object-term
				       (create-chaos-list
					  :list (possible-rewrites (meta-term-term T1)))) .
    eq is-variable(T1:*Term*) = #!! (coerce-to-bool (term-is-variable? (meta-term-term T1))) .
    eq is-application-form(T1:*Term*) = #!! (coerce-to-bool (term-is-applform? (meta-term-term T1))) .
    eq is-builtin-constant(T1:*Term*) = #!! (coerce-to-bool (term-is-builtin-constant? (meta-term-term T1))) .
    eq is-p-constant(T1:*Term*) = #!! (coerce-to-bool (term-is-psuedo-constant? (meta-term-term T1))) .
    eq is-system-object(T1:*Term*) = #!! (coerce-to-bool (term-is-system-object? (meta-term-term T1))) .
    eq T1:*Term* ==  T2:*Term* = term(T1) == term(T2) .
    eq (T1:*Term* = T2:*Term*) = (term(T1) = term(T2)) .
    eq operator(T1:*Term*) = #!! (create-system-object-term (term-head (meta-term-term T1))) .
    eq sort-of(T1:*Term*) = #!! (create-system-object-term (term-sort (meta-term-term T1))) .
    eq subterm(X:Nat, T1:*Term*) = #!! (make-meta-term (term-arg-n (meta-term-term T1) (term-builtin-value X))) .
    eq subterms(T1:*Term*) = #!! (create-system-object-term (make-chaos-list :list
							       (mapcar #'(lambda (x) (make-meta-term x)) (term-subterms (meta-term-term T1))))) .
    eq parse(S:String) = #!! (create-system-object-term (simple-parse-from-string(term-builtin-value S))) .
    eq subterm(T1:*Term*, Oc:*Occurence*) = #!! (meta-occur-at T1 Oc) .
    eq reduce(T1:*Term*) = term(T1) .
    eq reduce(T1:String) = #!! (perform-meta-reduction (term-builtin-value T1) *current-module* :red) .
    eq (reduce in M:*Module* : T1:String) = #!! (perform-meta-reduction (term-builtin-value T1) (term-system-object M) :red) .
  }
}

module CHAOS:AXIOM {
  imports {
    protecting(CHAOS:TERM)
  }
  signature {
    [ String < *Occurence* ]
    [ String < *AxiomSpec* ]
    op [:axiom_] : *Label* -> *Axiom*
    op [:axiom__] : *Label* *Module* -> *Axiom*
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
    op read  : String -> *ChaosExpr*
    op eval  : *ChaosExpr* -> *ChaosObject*
    op rep   : String -> *ChaosObject*
    op apply_to_ : *AxiomSpec* *Term* -> *Cosmos*
    op apply_to_at_ : *AxiomSpec* *Term* *Occurence* -> *Cosmos*
  }
  axioms {
    eq read(X:String) =
      #!! (create-system-object-term (parse-cafeobj-input-from-string (term-builtin-value X))) .
    eq eval(X:*ChaosExpr*) =
      #!! (create-system-object-term (eval-ast (term-system-object X))) .
    eq rep(X:String) = eval(read(X)) .
    eq apply A:*AxiomSpec* to T1:*Term* = rep("apply " ++ A ++ "to" ++ [:str (term(T1))]) .
  }
}

evq 
(let ((meta-mod (eval-modexp "METALEVEL")))
  (with-in-module (meta-mod)
    (let* ((term-op (find-operator '("'" "[" "_" "]") 1 *current-module*))
	   (term-meth (lowest-method* (car (opinfo-methods term-op)))))
       (setq *op-term* term-meth))))

eof
--

