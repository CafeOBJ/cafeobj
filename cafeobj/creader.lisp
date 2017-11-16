;;;-*- Mode: Lisp; Syntax:Common-Lisp; Package:CHAOS; Base:10 -*-
;;;
;;; Copyright (c) 2000-2016, Toshimi Sawada. All rights reserved.
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#|=============================================================================
                            System:CHAOS
                           Module: cafeobj
                         File: creader.lisp
==============================================================================|#

;;;=============================================================================
;;; Schema based generalized reader based on OBJ3 implementation.
;;;=============================================================================

;;;
;;; TOP-LEVEL module parser invokes 'reader' with schemas for modules

(defun cafeobj-parse ()
  (reader 'Top-form *cafeobj-schemas*))

(defun cafeobj-parse-from-string (str)
  (with-input-from-string (stream str)
    (let ((*standard-input* stream))
      (cafeobj-parse))))


;;; SCHEMA
;;;  schema for top-level of CafeOBJ ===========================================

;;;=============================================================================
;;; CafeOBJ Schemas
;;;-----------------------------------------------------------------------------

(eval-when (:execute :compile-toplevel :load-toplevel)

;;;-----------------------------------------------------------------------------
;;; SORT/SUBSORT DECLARATION
;;;-----------------------------------------------------------------------------

;;; VISIBLE SORTS

  (defparameter SortDeclaration
      '(|[| (:upto (< |,| |]|) :sorts)
             :append (:seq-of (:one-of (<) (|,|))
                              (:upto (< |,| |]|) :sorts))
             |]|))

;;; HIDDEN SORTS

  (defparameter HSortDeclaration
      '(*
        (|[| (:upto (< |,| |]|) :sorts)
         :append (:seq-of (:one-of (<) (|,|))
                  (:upto (< |,| |]|) :sorts))
         |]|)
        *))

  (defparameter HRCSortDeclaration
      '(*record :symbol (:optional (:! Supers))
        |{|
        (:optional (:! Sv-pairs))
        |}|)
    )

;;; BUILTIN SORT

  (defparameter BSortDeclaration
      '(bsort :symbol (:call (read))))

;;; BUILTIN HIDDEN SORT

  (defparameter BHSortDeclaration
      '(hbsort :symbol (:call (read))))

;;;-----------------------------------------------------------------------------
;;; OPERATOR DECLARATION
;;;-----------------------------------------------------------------------------

;;; GENERAL OPERATORs

  (defparameter OperatorDeclaration
      '((:+ op ops) (:seq-of :opname) |:| :sorts -> :sort
        (:if-present
         |{| (:many-of
              ((:+ assoc comm idem associative commutative idempotent demod))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ;; ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (\(  (:seq-of :int)  \))
              ((:+ strat strategy |strat:| |strategy:|)
               \(  (:seq-of :int)  \))
              ((:+ l-assoc r-assoc left-associative right-associative))
              ((:+ constr ctor constructor))
              ((:+ coherent beh-coherent))
              (memo)
              )
         |}|
         )))

;;; BEHAVIOURAL OPERATOR DECLARATION

  (defparameter BOperatorDeclaration
      '((:+ bop bops) (:seq-of :opname) |:| :sorts -> :sort
        (:if-present
         |{| (:many-of
              ((:+ assoc comm idem associative commutative idempotent demod))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ;; ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (\(  (:seq-of :int)  \))
              ((:+ strat strategy |strat:| |strategy:|)
               \(  (:seq-of :int)  \))
              ((:+ l-assoc r-assoc left-associative right-associative))
              ((:+ constr constructor))
              (memo)
              )
         |}|
         )))

;;; PREDICATE -- short hand for bool-valued ops.

  (defparameter PredicateDeclaration
      '((:+ pred preds pd pds) (:seq-of :opname) |:|
        (:upto (op ops bop bops |[| pred preds pd pds bpred bpreds bpd bpds hidden signature sig
                axioms ax axiom imports dpred
                |{| |}| |.| -- ** --> **> class record eq rule rl ceq crule crl
                bq bcq beq bceq brule brl bcrule bcrl trans tr ctrans ctr btrans btr
                bctrans bctr fax bfax
                var vars parse ev evq lisp lispq let |#define|)
         :sorts)
        (:if-present
         |{| (:many-of
              ((:+ assoc comm idem associative commutative idempotent demod))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ;; ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (\(  (:seq-of :int)  \))
              ((:+ strat strategy |strat:| |strategy:|)
               \(  (:seq-of :int)  \))
              ((:+ l-assoc r-assoc left-associative right-associative))
              ((:+ constr constructor))
              ((:+ coherent beh-coherent))
              ((:+ meta-demod demod))
              (memo)
              )
         |}|
         )))

  (defparameter BPredicateDeclaration
      '((+ bpred bpreds bpd bpds) (:seq-of :opname) |:|
        (:upto (op ops bop bops |[| pred preds pd pds bpred bpreds bpd bpds hidden signature sig
                axioms ax axiom imports dpred
                |{| |}| |.| -- ** --> **> class record eq rule rl ceq crule crl
                bq bcq beq bceq brule brl bcrule bcrl trans tr ctrans ctr btrans btr
                bctrans bctr fax bfax
                var vars parse ev evq lisp lispq let |#define|)
         :sorts)
        (:if-present
         |{| (:many-of
              ((:+ assoc comm idem associative commutative idempotent demod))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ;; ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (\(  (:seq-of :int)  \))
              ((:+ strat strategy |strat:| |strategy:|)
               \(  (:seq-of :int)  \))
              ((:+ l-assoc r-assoc left-associative right-associative))
              ((:+ constr constructor))
              ((:+ coherent beh-coherent))
              (memo)
              ((:+ demod meta-demod))
              )
         |}|
         )))
  
;;; OPERATOR ATTRIBUTES
;;; Now almost obsolate.

  (defparameter OperatorAttribute
      '((:+ attr attrs) (:seq-of :opname)
        |{|
        (:many-of
         ((:+ assoc comm idem associative commutative idempotent demod))
         (|id:| :chaos-item)
         (|identity:| :chaos-item)
         (|idr:| :chaos-item)
         (|identity-rules:| :chaos-item)
         ;; ((:pred general-read-numberp))
         ((:+ prec precedence |prec:| |pecedence:|) :int)
         (\(  (:seq-of :int)  \))
         ((:+ strat strategy |strat:| |strategy:|) \(  (:seq-of :int)  \))
         ((:+ l-assoc r-assoc))
         ;; ((:+ constr constructor))
         (memo)
         )
        |}|))

;;;-----------------------------------------------------------------------------
;;; LET
;;;-----------------------------------------------------------------------------

  (defparameter LetDeclaration
      '(let :symbol (:optional |:| :sort) = :term |.|))

;;;-----------------------------------------------------------------------------
;;; VARIABLE DECLARATION
;;;-----------------------------------------------------------------------------
  (defparameter VarDeclaration
      '(var :symbol |:| :sort))
  (defparameter VarsDeclaration
      '(vars :symbols |:| :sort))
  (defparameter PVarDeclaration
      '(pvar :symbol |:| :sort))
  (defparameter PVarsDeclaration
      '(pvars :symbols |:| :sort))

;;;-----------------------------------------------------------------------------
;;; MACRO
;;;-----------------------------------------------------------------------------
  (defparameter MacroDeclaration
      '(|#define| :term |::=| :term |.|))

;;;-----------------------------------------------------------------------------
;;; AXIOMS
;;;-----------------------------------------------------------------------------

;;; EQUATION

  (defparameter EqDeclaration
      '(eq :term = :term |.|))
  (defparameter BEqDeclaration
      '((:+ beq bq) :term = :term |.|))
  (defparameter CEQDeclaration
      '((:+ ceq cq) :term = :term if :term |.|))
  (defparameter BCEQDeclaration
      '((:+ bceq bcq) :term = :term if :term |.|))
  (defparameter FoplAXDeclaration
      '((:+ fax bfax ax bax frm bfrm) :term |.|))
  (defparameter FoplGoalDeclaration
      '((:+ goal bgoal) :term |.|))

;;; STATE TRANSITION

  (defparameter RlDeclaration
      '((:+ rule rl trans tr) :term => :term |.|))
  (defparameter BRLDeclaration
      '((:+ brule brl btrans btr) :term => :term |.|))
  (defparameter CRLDeclaration
      '((:+ crule crl ctrans ctr) :term => :term if :term |.|))
  (defparameter BCRLDeclaration
      '((:+ bcrule brl bctrans bctr) :term => :term if :term |.|))

;;;-----------------------------------------------------------------------------
;;; IMPORTATIONS
;;;-----------------------------------------------------------------------------

  (defparameter ExDeclaration
      '((:+ ex extending) (:if-present as :symbol) \(  :modexp  \)))
  (defparameter PrDeclaration
      '((:+ pr protecting) (:if-present as :symbol) \(  :modexp  \)))
  (defparameter UsDeclaration
      '((:+ us using) (:if-present as :symbol) \(  :modexp  \)))
  (defparameter IncDeclaration
      '((:+ inc including) (:if-present as :symbol) \(  :modexp  \)))

  )

;;;-----------------------------------------------------------------------------
;;; CITP tactics
;;;-----------------------------------------------------------------------------
(eval-when (:execute :compile-toplevel :load-toplevel)
  (defparameter CTF
      '((:+ |:ctf| |:ctf-|)
        (:one-of (|{| (:one-of #.EqDeclaration 
                               #.BeqDeclaration
                               #.FoplAXDeclaration)
                  |}|)
               (\[ :term |.| \]))))

  (defparameter CSP
      '((:+ |:csp| |:csp-|)
        |{| (:many-of  #.EqDeclaration
                       #.RlDeclaration
                       #.BeqDeclaration
                       #.BRLDeclaration
                       #.FoplAXDeclaration)
        |}|))

  (defparameter INIT
      '((:+ |:init| init |:init!| init!) 
        (:if-present as :symbol)
        (:one-of (\( (:one-of #.EqDeclaration
                              #.CeqDeclaration
                              #.RlDeclaration
                              #.CRlDeclaration
                              #.BeqDeclaration
                              #.BCeqDeclaration
                              #.BRLDeclaration
                              #.BCRLDeclaration
                              #.FoplAXDeclaration)
                  \))
                 (\[ (:symbol) \]))
        |by| |{| ((:! SubstList)) |}|))
  (defparameter USE
      '(|:use|
        (:one-of (\( (:seq-of :symbol) \))
                 (\[ :symbol \] 
                  |{| (:many-of ((:+ assoc comm associative commutative))
                                (|id:| :chaos-item)
                                (|identity:| :chaos-item))
                  |}|))))
  (defparameter EMBED
      '(|:embed| 
        (:one-of (\( (:seq-of :symbol) \) (:+ as into) :symbol)
                 (\[ :symbol \]
                  |{| (:many-of ((:+ assoc comm associative commutative))
                                (|id:| :chaos-item)
                                (|identity:| :chaos-item))
                  |}| (:+ as into) :symbol))))

  (defparameter IND
      '((:+ |:ind| |:induction|)
        (:one-of (on \( (:seq-of :term) \))
                 (\{ (on \( (:seq-of :term) \))
                     (base \( (:upto (|.| \)) :term)
                           :append (:seq-of |.|
                                      (:upto (|.| \)) :term))
                           \))
                  (:if-present hypo
                   \( (:upto (|.| \)) :term )
                           :append (:seq-of |.|
                                            (:upto (|.| \)) :term))
                        \))
                  (step \( (:upto (|.| \)) :term )
                           :append (:seq-of |.|
                                            (:upto (|.| \)) :term))
                        \))
                  \}))))
  (defparameter CITPATTR
      '(|:theory| (:seq-of :opname) |:| :sorts -> :sort
        |{| (:many-of ((:+ assoc comm associative commutative))
             (|id:| :chaos-item))
        |}|))
)

;;;-----------------------------------------------------------------------------
;;; THE SCHEME OF WHOLE ALLOWABLE INPUTS
;;;-----------------------------------------------------------------------------

(eval-when (:execute :load-toplevel)
  (setq *cafeobj-schemas*
    '(
      (Top-form
       (:one-of
        (;; MODULE : Its Constructs
         ;; --------------------------------------------------
         (:+ mod module module* module! mod* mod! 
             |sys:mod| |sys:mod*| |sys:mod!|
             |sys:module| |sys:module*| |sys:module!|
             |hwd:module!| |hwd:module*| |hwd:module|
             ots |sys:ots| |hwd:ots|
             )
         :symbol                        ; (:optional (:! Params))
         (:if-present (:+ \( \[) (:! Param) :append (:seq-of |,| (:! Param))
                      (:+ \) \]))
         (:if-present (:+ principal-sort psort p-sort) :sort)
         |{|
         (:many-of
          ;; MODULE IMPORTATIONS
          ;; *NOTE*  imports { ... } is not in MANUAL, and does not have
          ;;         translater to Chaos now.
          ((:+ imports import)
           |{|
           (:many-of
            #.ExDeclaration
            #.PrDeclaration
            #.UsDeclaration
            #.IncDeclaration
            ((:+ --> **>) :comment)
            ((:+ -- **) :comment)
            )
           |}|)
          #.ExDeclaration
          #.PrDeclaration
          #.UsDeclaration
          #.IncDeclaration

          ;; SIGNATURE
          ((:+ sig signature) |{|
                              (:many-of
                               #.BSortDeclaration
                               #.BHSortDeclaration
                               #.HSortDeclaration
                               #.SortDeclaration
                               #.OperatorDeclaration
                               #.BOperatorDeclaration
                               #.PredicateDeclaration
                               #.BPredicateDeclaration
                               #.OperatorAttribute
                               ;; #.R-C-Declaration
                               ((:+ --> **>) :comment)
                               ((:+ -- **) :comment)
                               )
                              |}|)

          ;; AXIOMS
          ((:+ axiom axioms axs) |{|
                                 (:many-of
                                  #.LetDeclaration
                                  #.MacroDeclaration
                                  #.VarDeclaration
                                  #.VarsDeclaration
                                  #.EqDeclaration
                                  #.CeqDeclaration
                                  #.RlDeclaration
                                  #.CRlDeclaration
                                  #.BeqDeclaration
                                  #.BCeqDeclaration
                                  #.BRLDeclaration
                                  #.BCRLDeclaration
                                  #.FoplAXDeclaration
                                  #.FoplGoalDeclaration
                                  ((:+ --> **>) :comment)
                                  ((:+ -- **) :comment)
                                  )
                                 |}|)

          ;; Module elements without signature/axioms.
          #.BSortDeclaration
          #.BHSortDeclaration
          #.SortDeclaration
          #.HSortDeclaration
          #.BHSortDeclaration
          ;; #.R-C-Declaration
          #.OperatorDeclaration
          #.BOperatorDeclaration
          #.PredicateDeclaration
          #.BPredicateDeclaration
          #.OperatorAttribute
          #.LetDeclaration
          #.MacroDeclaration
          #.VarDeclaration
          #.VarsDeclaration
          #.EqDeclaration
          #.BEqDeclaration
          #.CeqDeclaration
          #.BCeqDeclaration
          #.RlDeclaration
          #.CRlDeclaration
          #.BRlDeclaration
          #.BCRLDeclaration
          #.FoplAXDeclaration
          #.FoplGoalDeclaration
          ((:+ --> **>) :comment)
          ((:+ -- **) :comment)

          ;; Misc elements.
          ;; (parse :term |.|)
          ((:+ ev lisp evq lispq) (:call (read)))
          ;; allow sole ".", and do nothing
          (|.|)
          )
         |}|
         )                              ; end module

        ;; VIEW DECLARATION
        ;; --------------------------------------------------
        (view :symbol 
              :modexp
              |}|)

        ;; MAKE
        ;; --------------------------------------------------
        (make :symbol \( :modexp \))

        ;; TOP LEVEL COMMANDS
        ;; --------------------------------------------------
        ((:+ reduce red execute exec exec! execute! breduce bred)
         (:rdr #..term-delimiting-chars. (:if-present  in :modexp |:|)) (:seq-of :term) |.|)
        (tram (:+ compile execute exec red reduce reset)
              (:if-present in :modexp |:|)
              (:seq-of :term) |.|)
        ((:+ cbred)
         (:if-present in :modexp |:|)
         (:seq-of :term) |.|)
        (version)
        ;; AUTO LOAD
        (autoload :symbol :symbol)
        (no-autoload :symbol)
        ;; (stop at :term |.|)
        ;; ((:+ rwt) limit :symbol)
        (test (:+ reduction red execution exec) (:if-present in :modexp |:|)
              (:seq-of :term)
              (:+ |:expect| |expect:| expect) (:seq-of :term) |.|)
        ;; ((:+ match unify) (:seq-of :term) (:+ to :to) (:seq-of :term) |.|)
        (match :term (:+ to with) :term |.|)
        (unify :term (:+ to with) :term |.|)
        ;; (call-that :symbol)
        ;; ((:+ language lang) :symbol)
        ((:+ input in) :symbol)
        (check (:seq-of :top-opname))
        (regularize (:seq-of :top-opname))
        (save :symbol)
        (restore :symbol)
        (prelude :symbol)
        (save-system :symbol)
        (protect (:seq-of :top-opname))
        (unprotect (:seq-of :top-opname))
        (clean memo)
        (reset)
        (full-reset)
        (full reset)
        ((:+ --> **>) :comment)
        ((:+ -- **) :comment)
        (parse (:rdr #..term-delimiting-chars.
                     (:if-present  in :modexp |:|) (:seq-of :term) |.|))
        ((:+ lisp ev eval evq lispq)
         (:call (read)))
        (set
         (:seq-of :top-opname))
        ((:+ show sh select describe desc :sh :show) :args)

        ;; module elements which can appear at top(iff a module is opened.)
        #.PrDeclaration
        #.ExDeclaration
        #.UsDeclaration
        #.IncDeclaration
        #.BSortDeclaration
        #.BHSortDeclaration
        #.HSortDeclaration
        #.SortDeclaration
        #.OperatorDeclaration
        #.BOperatorDeclaration
        #.PredicateDeclaration
        #.BPredicateDeclaration
        #.LetDeclaration
        #.MacroDeclaration
        #.VarDeclaration
        #.VarsDeclaration
        #.PVarDeclaration
        #.PVarsDeclaration
        #.EqDeclaration
        #.CEqDeclaration
        #.BEqDeclaration
        #.BCEqDeclaration
        #.RlDeclaration
        #.CRlDeclaration
        #.BRlDeclaration
        #.BCRLDeclaration
        #.FoplAXDeclaration
        #.FoplGoalDeclaration
        ;; theorem proving stuff.
        ;; (open (:seq-of :top-opname))
        (open :modexp |.|)
        (close)
        (start :term |.|)
        ;; scase (<Term>) on (<Modexp>) as <Name> { <ModuleElements> } : <GoalTerm> .
        (scase \( (:seq-of :term) \) in \( :modexp \) as :symbol |{|
               (:many-of
                ;; MODULE IMPORTATIONS
                ;; *NOTE*  imports { ... } is not in MANUAL, and does not have
                ;;         translater to Chaos now.
                ((:+ imports import)
                 |{|
                 (:many-of
                  #.ExDeclaration
                  #.PrDeclaration
                  #.UsDeclaration
                  #.IncDeclaration
                  ((:+ --> **>) :comment)
                  ((:+ -- **) :comment)
                  )
                 |}|)
                #.ExDeclaration
                #.PrDeclaration
                #.UsDeclaration
                #.IncDeclaration
                
                ;; SIGNATURE
                ((:+ sig signature) |{|
                                    (:many-of
                                     #.BSortDeclaration
                                     #.BHSortDeclaration
                                     #.HSortDeclaration
                                     #.SortDeclaration
                                     #.OperatorDeclaration
                                     #.BOperatorDeclaration
                                     #.PredicateDeclaration
                                     #.BPredicateDeclaration
                                     #.OperatorAttribute
                                     ;; #.R-C-Declaration
                                     ((:+ --> **>) :comment)
                                     ((:+ -- **) :comment)
                                     )
                                    |}|)

                ;; AXIOMS
                ((:+ axiom axioms axs) |{|
                                       (:many-of
                                        #.LetDeclaration
                                        #.MacroDeclaration
                                        #.VarDeclaration
                                        #.VarsDeclaration
                                        #.EqDeclaration
                                        #.CeqDeclaration
                                        #.RlDeclaration
                                        #.CRlDeclaration
                                        #.BeqDeclaration
                                        #.BCeqDeclaration
                                        #.BRLDeclaration
                                        #.BCRLDeclaration
                                        #.FoplAXDeclaration
                                        #.FoplGoalDeclaration
                                        ((:+ --> **>) :comment)
                                        ((:+ -- **) :comment)
                                        )
                                       |}|)

                ;; Module elements without signature/axioms.
                #.BSortDeclaration
                #.BHSortDeclaration
                #.SortDeclaration
                #.HSortDeclaration
                #.BHSortDeclaration
                ;; #.R-C-Declaration
                #.OperatorDeclaration
                #.BOperatorDeclaration
                #.PredicateDeclaration
                #.BPredicateDeclaration
                #.OperatorAttribute
                #.LetDeclaration
                #.MacroDeclaration
                #.VarDeclaration
                #.VarsDeclaration
                #.EqDeclaration
                #.BEqDeclaration
                #.CeqDeclaration
                #.BCeqDeclaration
                #.RlDeclaration
                #.CRlDeclaration
                #.BRlDeclaration
                #.BCRLDeclaration
                #.FoplAXDeclaration
                #.FoplGoalDeclaration
                ((:+ --> **>) :comment)
                ((:+ -- **) :comment)
                
                ;; Misc elements.
                ;; (parse :term |.|)
                ((:+ ev lisp evq lispq) (:call (read)))
                ;; allow sole ".", and do nothing
                (|.|)
                )
               |}|
               |:| (:seq-of :term) |.|)
        ;; trace/untrace
        ((:+ trace untrace) :symbol)
        ;; apply
        (apply (:one-of-default
                (:symbol (:upto
                          (within at)
                          (:optional with :symbol
                                     = (:upto (|,| within at) :term)
                                     :append
                                     (:seq-of |,| :symbol
                                              = (:upto (|,| within at) :term))))
                         (:+ within at)
                         (:one-of
                          ((:+ top it term subterm))
                          ((:+ \( |{| \[)
                           :unread
                           ((:! Selector))
                           (:seq-of of ((:! Selector)))
                           |.|)))
                (?)))
        ;;
        (choose (:one-of
                 ((:+ top term subterm))
                 ((:+ \( |{| \[)
                  :unread
                  ((:! Selector))
                  (:seq-of of ((:! Selector)))
                  |.|)))

        (find (:+ rule -rule +rule rules -rules +rules))
        ;; RWL related commands
        ((:+ cont continue) :args)
        
        ;; PROVIDE/REQUIRE
        (provide :symbol)
        (require :top-term)
        (autoload :symbol :symbol)
        ;; for testing delimiters
        (delimiter (:+ = + -)
                   |{|
                   (:upto (|}|) :chars)
                   :append (:seq-of (:upto (|}|) :chars))
                   |}|)
        ;;
        (delim)
        ;; PigNose commands
        #+:bigpink (db reset)
        #+:bigpink ((:+ sos passive) (:+ = + -)
                                     |{|
                                     (:upto (|,| |}|) :sorts)
                                     :append (:seq-of |,|
                                                      (:upto (|}| |,|) :sorts))
                                     |}|)
        #+:bigpink (list
                    (:+ axiom axioms
                        sos usable
                        flag param flags parameter parameters
                        option options passive
                        demod demodulator demodulators))
        #+:bigpink (clause :term |.|)
        #+:bigpink (option (:one-of (reset)
                                    (= :symbol)))
        #+:bigpink ((:+ save-option save-options) :symbol)
        #+:bigpink (flag \(  :symbol |,| (:+ on off set clear)  \))
        #+:bigpink (param \(  :symbol |,| :int  \))
        #+:bigpink (resolve :args)
        #+:bigpink (demod (:if-present  in :modexp |:|) (:seq-of :term) |.|)
        #+:bigpink (sigmatch \( :modexp \) (:+ to with) \( :modexp \))

        #+:bigpink (lex \(
                        (:upto (|,| \)) :opname)
                        :append (:seq-of |,|
                                         (:upto (|,| \)) :opname))
                        \))
        ;; misc toplevel commands
        (eof)
        #-CMU (#\^D)
        #+CMU (#\)
        ;; (prompt (:seq-of :top-opname))
        ((:+ quit q |:q| |:quit|))
        (cd :args)
        (pushd :args)
        (popd :args)
        (dirs)
        ;; #-(or GCL LUCID CMU) (ls :symbol)
        ;; #+(or GCL LUCID CMU) 
        ;; (ls :top-opname)
        (ls :args)
        (dribble :symbol)
        (pwd)
        (! :top-term)                   ; shell escape
        (|.|)
        ;; (chaos :args)
        ;; new commands as of 2011/Q1
        (? :args)                       ; help/messege description
        (?? :args)                      ; detailed help
        ;; new commands as of 2012/Q1
        ((:+ names name) :modexp |.|)
        (look up (:if-present in :modexp |:|) (:seq-of :top-opname))
        ;; term inspector
        ((:+ inspect inspect-term) :args)
        ;; generate reference manual
        (gendoc :symbol)
        (?example :args)
        (?ex :args)
        (?apropos :comment)
        (?ap :comment)
        ((:+ ?com ?command) :args)
        ((:+ command commands com))
        ;; CITP commands
        (|:goal| |{| (:many-of  #.EqDeclaration
                                #.CeqDeclaration
                                #.RlDeclaration
                                #.CRlDeclaration
                                #.BeqDeclaration
                                #.BCeqDeclaration
                                #.BRLDeclaration
                                #.BCRLDeclaration
                                #.FoplAXDeclaration)
                 |}|)
        (|:apply| (:if-present to (:symbol)) (\( (:seq-of :symbol) \)))
        (|:auto|)
        #.IND
        (|:roll| (:+ back |:back|))
        #.INIT
        ((:+ |:imply| |:imp|) (\[ (:symbol) \])
                              (:one-of (|by| |{| ((:! SubstList)) |}|)
                                       (|.|)))
        (|:cp| (:one-of (\( (:one-of #.EqDeclaration
                                      #.CeqDeclaration
                                      #.RlDeclaration
                                      #.CRlDeclaration
                                      #.BeqDeclaration
                                      #.BCeqDeclaration
                                      #.BRLDeclaration
                                      #.BCRLDeclaration
                                      #.FoplGoalDeclaration)
                             \))
                        (\[ (:symbol) \]))
               ><
               (:one-of (\( (:one-of #.EqDeclaration
                                      #.CeqDeclaration
                                      #.RlDeclaration
                                      #.CRlDeclaration
                                      #.BeqDeclaration
                                      #.BCeqDeclaration
                                      #.BRLDeclaration
                                      #.BCRLDeclaration
                                      #.FoplGoalDeclaration)
                             \))
                        (\[ (:symbol) \])))
        ((:+ |:equation| |:rule|))
        (|:backward| (:+ equation rule |:equation| |:rule|))
        (|:select| (:symbol))
        ((:+ |:red| |lred| |:lred| |:exec| |:bred|)
         (:rdr #..term-delimiting-chars. (:if-present  in :symbol |:|)) (:seq-of :term) |.|)
        (|:verbose| :symbol)
        #.CTF
        #.CSP
        #.CITPATTR
        ((:+ |:show| |:sh| |:describe| |:desc|) :args)
        ((:+ |:def| |:define|) :symbol = (:one-of #.CTF
                                                  #.CSP
                                                  #.INIT  
                                                  (\( (:seq-of :symbol) \))))
        (|:spoiler| (:one-of (on) (off) (|.|)))
        (|:binspect|
         (:rdr #..term-delimiting-chars. (:if-present in :symbol |:|)) (:seq-of :term) |.|)
        (binspect
         (:rdr #..term-delimiting-chars. (:if-present  in :modexp |:|)) (:seq-of :term) |.|)
        ((:+ |:bresolve| bresolve) :args)
        ((:+ |:bshow| bshow) :args)
        ((:+ |:bg| |:bguess| bg bguess) :args)
        (|:set| \(  :symbol |,| (:+ on off set clear ? show)  \))
        (|:order| \(
                        (:upto (|,| \)) :opname)
                        :append (:seq-of |,|
                                         (:upto (|,| \)) :opname))
                        \))
        #.USE
        #.EMBED
        (|:reset|)
        ))                              ; end Top-Form

      ;; some separated definitions of non-terminals.
      ;; --------------------------------------------------
      ;; subterm specifier
      
      (Selector (:one-of 
                 (|{| :int :append (:seq-of |,| :int) |}|)
                 (\(  (:seq-of :int)  \))
                 (\[ :int (:optional |..| :int) \])))

      ;; parameter part
      ;; (Params (\[ (:! Param) :append (:seq-of |,| (:! Param)) \]))
      (Param  (:one-of-default
               (:symbols |::| (:upto (|,| \] \)) :modexp))
               ((:+ ex extending us using pr protecting inc including)
                :symbols |::| (:upto (|,| \] \)) :modexp))))

      ;; Substitution
      ;;  variable-1 <- term-1; ... variable-n <- term-n;
      (SubstList ((:! Subst) :append (:seq-of (:! Subst))))
      (Subst ((:symbol <- :term) \;))
      ))                                ; end of *cafeobj-scheme*
  )                                     ; end eval-when


;;; EOF
