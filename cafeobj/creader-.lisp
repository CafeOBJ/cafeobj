;;;-*- Mode: Lisp; Syntax:CommonLisp; Package:CHAOS; Base:10 -*-
;;; $Id: creader.lisp,v 1.15 2010-08-09 00:43:37 sawada Exp $
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

;;; TOP-LEVEL module parser invokes 'reader' with schemas for modules

(defun cafeobj-parse ()
  (reader 'Top-form *cafeobj-schemas*))

;;; SCHEMA
;;;  schema for top-level of CafeOBJ ===========================================

;;;=============================================================================
;;; CafeOBJ Schemas
;;;-----------------------------------------------------------------------------

(eval-when (eval compile load)

;;;-----------------------------------------------------------------------------
;;; SORT/SUBSORT DECLARATION
;;;-----------------------------------------------------------------------------

;;; VISIBLE SORTS

  (defparameter SortDeclaration
      ' (|[| (:upto (< |,| |]|) :sorts)
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
              ((:+ assoc comm idem associative commutative idempotent))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (|(| (:seq-of :int) |)|)
              ((:+ strat strategy |strat:| |strategy:|)
               |(| (:seq-of :int) |)|)
              ((:+ l-assoc r-assoc left-associative right-associative))
              ((:+ constr constructor))
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
              ((:+ assoc comm idem associative commutative idempotent))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (|(| (:seq-of :int) |)|)
              ((:+ strat strategy |strat:| |strategy:|)
               |(| (:seq-of :int) |)|)
              ((:+ l-assoc r-assoc left-associative right-associative))
              ((:+ constr constructor))
              (memo)
              )
         |}|
         )))

;;; PREDICATE -- short hand for bool-valued ops.

  (defparameter PredicateDeclaration
      '(pred (:seq-of :opname) |:|
        (:upto (op ops bop bops |[| pred preds bpred bpreds hidden signature sig
                axioms ax axiom imports dpred
                |{| |}| |.| -- ** --> **> class record eq rule rl ceq crule crl
                bq bcq beq bceq brule brl bcrule bcrl trans trns btrans btrns
                bctrans bctrns fax bfax
                var vars parse ev evq lisp lispq let)
         :sorts)
        (:if-present
         |{| (:many-of
              ((:+ assoc comm idem associative commutative idempotent))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ;; ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (|(| (:seq-of :int) |)|)
              ((:+ strat strategy |strat:| |strategy:|)
               |(| (:seq-of :int) |)|)
              ((:+ l-assoc r-assoc left-associative right-associative))
              ((:+ constr constructor))
              ((:+ coherent beh-coherent))
              ((:+ meta-demod demod))
              (memo)
              )
         |}|
         )))

  (defparameter BPredicateDeclaration
      '(bpred (:seq-of :opname) |:|
        (:upto (op ops bop bops |[| pred preds bpred bpreds hidden signature sig
                axioms ax axiom imports 
                |{| |}| |.| -- ** --> **> class record eq rule rl ceq crule crl
                bq bcq beq bceq brule brl bcrule bcrl trans trns btrans btrns
                bctrans bctrns fax bfax
                var vars parse ev evq lisp lispq let)
         :sorts)
        (:if-present
         |{| (:many-of
              ((:+ assoc comm idem associative commutative idempotent))
              (|id:| :chaos-item)
              (|identity:| :chaos-item)
              (|idr:| :chaos-item)
              (|identity-rules:| :chaos-item)
              ;; ((:pred general-read-numberp))
              ((:+ prec precedence |prec:| |pecedence:|) :int)
              (|(| (:seq-of :int) |)|)
              ((:+ strat strategy |strat:| |strategy:|)
               |(| (:seq-of :int) |)|)
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
         ((:+ assoc comm idem associative commutative idempotent))
         (|id:| :chaos-item)
         (|identity:| :chaos-item)
         (|idr:| :chaos-item)
         (|identity-rules:| :chaos-item)
         ;; ((:pred general-read-numberp))
         ((:+ prec precedence |prec:| |pecedence:|) :int)
         (|(| (:seq-of :int) |)|)
         ((:+ strat strategy |strat:| |strategy:|) |(| (:seq-of :int) |)|)
         ((:+ l-assoc r-assoc))
         ;; ((:+ constr constructor))
         (memo)
         )
        |}|))

;;;-----------------------------------------------------------------------------
;;; RECORD DECLARATION
;;; *NOTE* class is not part of CafeOBJ language.
;;;-----------------------------------------------------------------------------

  (defparameter R-C-Declaration
      '((:+ record class) :symbol (:optional (:! Supers)) |{|
        (:optional (:! Sv-pairs))
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
      '(eq (:optional |[| (:seq-of :symbol (:upto (|]| |:|)))) :term = :term |.|))
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
      '((:+ rule rl trans trns) :term => :term |.|))
  (defparameter BRLDeclaration
      '((:+ brule brl btrans btrns) :term => :term |.|))
  (defparameter CRLDeclaration
      '((:+ crule crl ctrans ctrns) :term => :term if :term |.|))
  (defparameter BCRLDeclaration
      '((:+ bcrule brl bctrans bctrns) :term => :term if :term |.|))

;;;-----------------------------------------------------------------------------
;;; IMPORTATIONS
;;;-----------------------------------------------------------------------------

  (defparameter ExDeclaration
      '((:+ ex extending) |(| :modexp |)|))
  (defparameter PrDeclaration
      '((:+ pr protecting) |(| :modexp |)|))
  (defparameter UsDeclaration
      '((:+ us using) |(| :modexp |)|))
  (defparameter IncDeclaration
      '((:+ inc including) |(| :modexp |)|))

  )

;;;-----------------------------------------------------------------------------
;;; THE SCHEME OF WHOLE ALLOWABLE INPUTS
;;;-----------------------------------------------------------------------------

(eval-when (eval load)
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
         (:if-present principal-sort :sort)
         ;; (:if-present psort :sort)
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
                               #.R-C-Declaration
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
          #.R-C-Declaration
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
          (parse :term |.|)
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
        (make :symbol |(| :modexp |)|)

        ;; TOP LEVEL COMMANDS
        ;; --------------------------------------------------
        ((:+ reduce red execute exec exec! execute! breduce bred)
         (:if-present  in :modexp |:|) (:seq-of :term) |.|)
        (tram (:+ compile execute exec red reduce reset)
              (:if-present in :modexp |:|)
              (:seq-of :term) |.|)
        ((:+ cbred)
         (:if-present in :modexp |:|)
         (:seq-of :term) |.|)
        (version)
        ;;
        (autoload :symbol :symbol)
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
        (parse (:if-present  in :modexp |:|) (:seq-of :term) |.|)
        ((:+ lisp ev eval evq lispq)
         (:call (read)))
        (;; (:+ show sh set select describe desc) ; do 
         set
         (:seq-of :top-opname))
        ;; (select :modexp :args)
        ((:+ show sh select describe desc) :args)
        (trans-chaos (:seq-of :top-opname))

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
                          ((:+ |(| |{| |[|)
                           :unread
                           ((:! Selector))
                           (:seq-of of ((:! Selector)))
                           |.|)))
                (?)))
        ;;
        (choose (:one-of
                 ((:+ top term subterm))
                 ((:+ |(| |{| |[|)
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
        #+:bigpink (flag |(| :symbol |,| (:+ on off set clear) |)|)
        #+:bigpink (param |(| :symbol |,| :int |)|)
        #+:bigpink (resolve :args)
        #+:bigpink (demod (:if-present  in :modexp |:|) (:seq-of :term) |.|)
        #+:bigpink (sigmatch |(| :modexp |)| (:+ to with) |(| :modexp |)|)

        #+:bigpink (lex |(|
                        (:upto (|,| |)|) :opname)
                        :append (:seq-of |,|
                                         (:upto (|,| |)|) :opname))
                        |)|)
        ;; misc toplevel commands
        (eof)
        #-CMU (#\^D)
        #+CMU (#\)
        (prompt (:seq-of :top-opname))
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
        (? :args)                       ; help/messege description
        (?? :args)                      ; detailed help
        (|.|)
        (chaos :args)
        ))                              ; end Top-Form

      ;; some separated definitions of non-terminals.
      ;; --------------------------------------------------
      ;; subterm specifier
      
      (Selector
       (:one-of
        ;; (term) (top) (subterm)
        (|{| :int :append (:seq-of |,| :int) |}|)
        (|(| (:seq-of :int) |)|)
        (\[ :int (:optional |..| :int) \])))

      ;; parameter part
      ;; (Params (\[ (:! Param) :append (:seq-of |,| (:! Param)) \]))
      (Param 
       (:one-of-default
        (:symbols |::| (:upto (|,| \] \)) :modexp))
        ((:+ ex extending us using pr protecting inc including)
         :symbols |::| (:upto (|,| \] \)) :modexp))))

      ;; importation modexp
      #||
      (ImportModexp
       (:symbol :modexp))
      (IM (:one-of-default
           (:modexp)
           (|::| :modexp)))
      ||#
      ;; (sortConst
      ;;  (:one-of-default
      ;;   (:sorts)
      ;;  (:symbol = { :term |:| :sorts })))

      ;; super reference.
      (Supers (\[ (:! Super) :append (:seq-of |,| (:! Super)) \]))
      (Super ((:upto (|,| \]) :super)))
      ;; slot/value pairs
      (SV-Pairs
       ((:! Sv-pair) :append  (:seq-of (:! Sv-pair)) ;(:seq-of |,| (:! Sv-pair))
        ))
      (Sv-Pair
       (:one-of-default
        (:symbol (:upto (|}|))
         (:one-of (|:| :sort)
                  (= |(| :term |)| |:| :sort)))
        ((:+ -- **) :comment)
        ((:+ --> **>) :comment))
       )
      ))
  )


;;; EOF
