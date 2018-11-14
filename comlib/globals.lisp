;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2018, Toshimi Sawada. All rights reserved.
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
#|==============================================================================
                                 System: CHAOS
                                 Module: comlib
                               File: globals.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; This file gathers the declaration of global/special variables of CHAOS
;;; system.
;;;

;;;********************
;;; RUNTIME ENVIRONMENT_________________________________________________________
;;;********************
;;;
;;; In Chaos, all of the works are done in a `context'.
;;; A context is a dag of modules with importation relation as arrows,
;;; the top node (module) is called `current module'.
;;; 
;;; The current module and its some frequently accessed informations are
;;; bound to global variables providing run time environment.
;;;
;;;   *current-module*       : the current-module
;;;   *current-sort-order*   : transitive closure of sort relations of
;;;                            current-mdoule.
;;;   *current-opinfo-table* : operator information table of the current-module.
;;;   *current-ext-rule-table* : extented rules for A, and AC
;;;

(declaim (special *current-module*      ; the module currently the target of
                                        ; operations.
                  *current-sort-order*  ; closure of sort relations of current
                                        ; module.
                  *current-opinfo-table* ; operator information table of the
                                        ; current module.
                  *current-ext-rule-table*
                  *top-level-definition-in-progress*
                  *on-preparing-for-parsing* ; parsing preparation in progress
                  ))

(defvar *top-level-definition-in-progress* nil)

;;; *open-module* bounds the 'opening' module.
;;; 
(declaim (special *open-module*         ; the module crrently opened.
                  *last-before-open*    ; the module which was *last* before the
                                        ; currently opened module.
                  ))

(defvar *current-module* nil)
(defvar *current-sort-order* nil)
(defvar *current-opinfo-table* nil)
(defvar *current-ext-rule-table* nil)
(defvar *open-module* nil)
(defvar *last-before-open* nil)

;;; Feature for require & provide
;;;
(defvar *chaos-features* nil)

;;; Some top level flags & variables.--------------------------------------------

(declaim (special *chaos-verbose* *chaos-quiet* *chaos-input-source*))
(defvar *chaos-verbose* nil)
(defvar *chaos-quiet* nil)
(defvar *chaos-input-source* nil)       ; binds a file name when processing
                                        ; input from the file. 
(declaim (special *chaos-input-level*)
         (type fixnum
               *chaos-input-level*
               *chaos-input-nesting-limit*))

(defvar *chaos-input-level* 0)
(defvar *chaos-input-nesting-limit* 10)

(declaim (special *auto-context-change*))
(defvar *auto-context-change* nil)

(defvar *system-prelude-dir* nil)
(defvar *system-lib-dir* nil)
(defvar *system-ex-dir* nil)

;;; ***********************************
;;; CONTROLL FLAGS OF REWRITING PROCESS_________________________________________
;;; ***********************************

(declaim (special *trace-level*))
(declaim (type (integer 0 256) *trace-level*))
(defvar *trace-level* 0)
(declaim (special *self*))
(defvar *self* nil)
(defvar $$cond nil)
(defvar $$trace-rewrite nil)            ; flag, non-nil -> trace.
(defvar $$trace-rewrite-whole nil)      ; flag, non-nil -> trace whole.
(defvar $$trace-proof nil)              ; flag, non-nil -> trace CITP proof.
;;; *proof-tree* binds current proof tree structure
(defvar *proof-tree* nil)
(defvar *next-default-proof-node* nil)
(defvar *citp-verbose* nil)
(defvar *citp-normalize-instance* t)

(defvar *rewrite-stepping* nil)         ; flag, non-nil -> under stepping.
(declaim (type fixnum *rewrite-count-limit*))
(defvar *rewrite-count-limit* -1)
                                        ; flag, non-nil(integer) -> limitation
                                        ; for rewriting steps.
(defvar *rewrite-stop-pattern* nil)     ; flag, non-nil(term) -> stop rewriting
                                        ; iff matches to the pattern.
(defvar *steps-to-be-done* nil)         ; remaining steps before stop
(defvar $$mod 'void)
;;;
(defvar *old-context* nil)
(declaim (special *old-context*))
(declaim (special *allow-$$term*))
(defvar *allow-$$term* t)
(defvar $$term 'void)                   ; current target term, destructively
                                        ; modified
(defvar $$subterm nil)                  ; subterm of $$term selected
(defvar $$term-context nil)             ; context module of $$term
(defvar $$selection-stack nil)
(defvar $$action-stack nil)
;;;
(defvar $$norm 'void)
(defvar $$show-red nil)
(defvar *perform-on-demand-reduction* t)
(declaim (special *rewrite-exec-mode*))
(defvar *rewrite-exec-mode* nil)
(declaim (special *cexec-target*))
(defvar *cexec-target* nil)
(declaim (special *rewrite-exec-condition*))
(defvar *rewrite-exec-condition* nil)
(declaim (special *rewrite-semantic-reduce*)
         (type (or null (not null)) *rewrite-semantic-reduce))
(defvar *rewrite-semantic-reduce* nil)
(declaim (special *beh-rewrite*)
         (type (or null (not null)) *beh-rewrite*))
(defvar *beh-rewrite* nil)
(declaim (type fixnum *rule-count*)
         (special *rule-count*))
(defvar *rule-count* 0)
(defvar *show-stats* t)
(defvar *try-try* nil)
(defvar *reduce-conditions* nil)
(declaim (type fixnum $$trials))
(defvar $$trials 1)
(declaim (type fixnum $$matches)
         (special $$matches))
(defvar $$matches 0)
(defvar *on-reduction* t)
(defvar *reduce-builtin-eager* nil)
(declaim (type fixnum *condition-trial-limit*))
(defparameter .condition-trial-limit-default.
  #+GCL 240
  #-GCL 5500)
(defvar *condition-trial-limit* .condition-trial-limit-default.)

;;; MEL support
(defvar *mel-sort* nil)
(defvar *mel-always* nil)
;;; (defvar *mel-reduce* nil)

;;; :=
(defvar *m-pattern-subst* nil)

;; memoization
(defvar *memo-rewrite* t)               ; use memo mechanism
(defvar *clean-memo-in-normalize* t)
(defvar *always-memo* nil)
(declaim (special *term-memo-hash-hit*)
         (type fixnum *hash-hit*))
(defvar *term-memo-hash-hit* 0)
(declaim (special .hash-size.)
         (type fixnum .hash-size.))
(defvar .hash-size. 0)
(defvar *allow-illegal-beh-axiom* t)

;;;*********************
;;; REGULARIZING CONTROL_______________________________________________________
;;;*********************
(declaim (special *regularize-signature*))
(defvar *regularize-signature* nil)
(defvar *check-regularity* nil)

;;;********************
;;; COMPATIBILITY CHECK________________________________________________________
;;;********************
(declaim (special *check-compatibility*))
(defvar *check-compatibility* nil)

;;;***************
;;; SENSIBLE CHECK_____________________________________________________________
;;;***************
(declaim (special *check-sensibleness*))
(defvar *check-sensibleness* nil)

;;;**********
;;; COHERENCY__________________________________________________________________
;;;**********
(declaim (special *check-rwl-coherency*))
(defvar *check-rwl-coherency* nil)

;;;**************************
;;; BUILTIN OVERLOADING CHECK__________________________________________________
;;;**************************
(declaim (special *builtin-overloading-check*))
(defvar *builtin-overloading-check* t)

;;; Flags for printer control._________________________________________________
;;;***************************

(declaim (special *print-indent*))
(declaim (type fixnum
               *chaos-print-level*
               *print-line-limit*
               *chaos-print-length*
               *print-indent* *print-indent-increment*))
(defvar *module-all-rules-every* nil)
(defvar *fancy-print* t)
(defvar *print-term-struct* nil)
(defvar *print-xmode* :normal)
(defvar *show-mode* :cafeobj)           ; one of :chaos or :cafeobj
(defvar *print-indent* 0)
(defparameter *print-indent-increment* 1)
(defvar *print-explicit* nil)           ;if t then give more detail on sorts, etc.
(defvar *print-abbrev-mod* nil)         ; abbreviate module names
(defvar *print-abbrev-num* 0)
(defvar *print-abbrev-table* nil)
(defvar *print-abbrev-quals* nil)
(defvar *print-with-sort* nil)
(defvar *print-operator-table* nil)
(defvar *print-flag-module-values* nil)
(defvar *print-indent-contin* nil)
(defvar *print-line-limit* 2000)
(defvar *print-mode* nil)
(defvar *print-all-eqns* nil)
(defvar *print-exec-rule* nil)
(defvar *print-every-exec-finding* nil)
(defvar *print-ignore-mods* nil)
(defvar *chaos-print-level* 5)
(defvar *chaos-print-length* 100)
(defvar *chaos-print-errors* nil)
(defvar *chaos-input-quiet* nil)
(defvar *print-variables* nil)
(defvar *grind-bool-term* nil)
(declaim (special .file-col.)
         (type fixnum .file-col.))
(defvar .file-col. 0)
(declaim (type (or null fixnum) *term-print-depth*))
(defvar *term-print-depth* nil)
(defvar *show-tree-horizontal* nil)

;;; CafeOBJ variables
(defvar *cafeobj-batch* nil)
(defvar *cafeobj-input-quiet* nil)
(defvar $)
(defvar -cafeobj-load-time- nil)
(defvar *cafeobj-standard-prelude-path* nil)

;;; NOT USED
;;; GRAMMAR
;;; 
;;; *GRM.CURRENT* is a grammar to which the following operations are to be applied. 
;;;         define.grm-rule
;;;         grm.clear-rule
;;; set by 'in.grammar' operation.
;;;
;;;(defvar *grm.current* nil)

;;; *CHAOS.CURRENT-GRAMMAR* is a list of grammar with which the `grm.parse' works.
;;; set by 'use.grammar' operation. (see "term-parser.lisp")
;;;
;;; (defvar *chaos.current-grammar* nil)

;;; ERROR TAGS ----------------------------------------------------------------
;;; (defvar *module-not-found-error* 'Module-Not-found)
;;; (defvar *sort-not-found-error* 'sort-not-found)
;;; (defvar *operator-not-found-error* 'operator-not-found)
;;;

;;;=============================================================================
;;; BUILTIN SORTS
;;;=============================================================================
;; NAMES of Builtin sort.
(defconstant $name-sort '|*Sort*|)
(defconstant $name-gen-sort '|_ GeneralSort _|)
(defconstant $name-bi-sort '|*BuiltinSort*|)
(defconstant $name-identifier '|*Identifier*|)
(defconstant $name-cosmos '|*Cosmos*|)
(defconstant $name-universal '|*Universal*|)
(defconstant $name-huniversal '|*HUniversal*|)
(defconstant $name-term '|*Term*|)
(defconstant $name-bottom '|_ Bottom _|)
(defconstant $name-hbottom '|_ HBottom _|)
(defconstant $name-record '|_ Record _|)
(defconstant $name-class '|_ Class _|)
(defconstant $name-and-sort '|_ ^-Sort _|)
(defconstant $name-or-sort '|_ \|-Sort _|)
(defconstant $name-err-sort '|_ ?-Sort _|)
(defconstant $name-operator '|*Operator*|)
(defconstant $name-optheory '|*OpTheory*|)
(defconstant $name-module '|*Module*|)
(defconstant $name-signature '|*Signature*|)
(defconstant $name-axiomset '|*AxiomSet*|)
(defconstant $name-trs '|*Trs*|)
(defconstant $name-axiom '|*Axiom*|)
(defconstant $name-chaos-object '|*ChaosObject*|)
(defconstant $name-chaos-expr '|*CafeExpr*|)
(defconstant $name-term-type '|*TermType*|)
(defconstant $name-chaos-list '|*CafeList*|)
(defconstant $name-void '|*Void*|)
(defconstant $name-import '|*Import*|)
(defconstant $name-subst '|*Substitution*|)
(defconstant $name-parameter '|*Parameter*|)

;;; builtin sorts
(defvar *cosmos* 'void)                 ; the whole 
(defvar *chaos-object* 'void)
(defvar *chaos-expr-sort* 'void)
(defvar *term-sort* 'void)
(defvar *universal-sort* 'void)         ; visible universe
(defvar *huniversal-sort* 'void)        ; hidden universe
(defvar *bottom-sort* 'void)            ; visible bottom sort
(defvar *hbottom-sort* 'void)           ; hidden bottom sort
(defvar *sort-sort* 'void)
(defvar *general-sort* 'void)
(defvar *builtin-sort* 'void)
(defvar *identifier-sort* 'void)
(defvar *id-sort* 'void)
(defvar *qid-sort* 'void)
(defvar *syntax-err-sort* 'void)
(defvar *type-err-sort* 'void)
(defvar *op-err-sort* 'void)
(defvar *and-sort* 'void)
(defvar *or-sort* 'void)
(defvar *err-sort* 'void)
(defvar *sort-error* 'none)
(defvar *record-sort* 'void)
(defvar *class-sort* 'void)
(defvar *operator-sort* 'void)
(defvar *optheory-sort* 'void)
(defvar *module-sort* 'void)
(defvar *import-sort* 'void)
(defvar *signature-sort* 'void)
(defvar *axiomset-sort* 'void)
(defvar *trs-sort* 'void)
(defvar *variable-sort* 'void)
(defvar *appl-form-sort* 'void)
(defvar *pvariable-sort* 'void)
(defvar *lisp-term-sort* 'void)
(defvar *slisp-term-sort* 'void)
(defvar *glisp-term-sort* 'void)
(defvar *bconst-term-sort* 'void)
(defvar *modexpr-sort* 'void)
(defvar *chaos-list-sort* 'void)
(defvar *chaos-void-sort* 'void)
(defvar *bool-sort* 'void)
(defvar *sort-id-sort* 'void)
(defvar *string-sort* 'void)
(defvar *chaos-value-sort* 'void)
(defvar *character-sort* 'void)
(defvar *axiom-sort* 'void)
(defvar *object-identifier-sort* 'void)
(defvar *object-sort* 'void)
(defvar *record-instance-sort* 'void)
(defvar *class-id-sort* 'void)
(defvar *record-id-sort* 'void)
(defvar *attribute-id-sort* 'void)
(defvar *attribute-sort* 'void)
(defvar *attribute-list-sort* 'void)
(defvar *attr-value-sort* 'void)
(defvar *message-sort* 'void)
(defvar *configuration-sort* 'void)
(defvar *acz-configuration-sort* 'void)
(defvar *subst-sort* 'void)
(defvar *sort_builtin* 'void)
(defvar *parameter-sort* 'void)
(defvar *condition-sort* 'void)
(defvar sup-universal-sort-name nil)
(defvar sup-huniversal-sort-name nil)

;;;=============================================================================
;;; Builtin modules & operations.
;;; Operations in some builtin modules.
;;;=============================================================================

(defvar *system-standard-prelude* nil)
(defvar *system-soft-wired* nil)
(defvar *kernel-hard-wired-builtin-modules* nil)

;;; *SYSTEM-MODULE*
(defvar *system-module* nil)

;;; *CHAOS-MODULE*
;;; bounds built in module CHAOS.
(defvar *chaos-meta* nil)
(defvar *chaos-module* nil)
(defvar *chaos-object-module* nil)
(defvar *builtin-metalevel-sort* (make-hash-table))
;;; 
(defvar *string-not-found* nil)

;;; *CHAOS-SORT-ORDER* holds the transitive closure of sort relations between
;;; builtin sorts. This is a value of slot 'sort-order' of builtin module
;;; CHAOS (buoud to global *chaos-module*).
;;;
(defvar *chaos-sort-order* 'void)

;;; *PARSER-SORT-ORDER*
(defvar *parser-sort-order* 'void)
  
;;; HARD-WIRED CHAOS MODULE
(defvar *system-object-module* nil)
(defvar *identifier-module* nil)
(defvar *universal-module* nil)
(defvar *parser-module* nil)
(defvar *qid-module* nil)
(defvar *id-module* nil)
(defvar .int-module. nil)

;;; Some operators & methods of CHAOS module.
;;; these are used for representing builtin constant and ill-formed terms
;;; at parsing time.
;;;
(defvar *builtin-method* nil)
(defvar *builtin-op* nil)
(defvar *partial-op* nil)
(defvar *void-op* nil)
(defvar *partial-method* nil)
(defvar *void-method* nil)
(defvar *type-err-op* nil)
(defvar *type-err-method* nil)
(defvar *op-err-op* nil)
(defvar *op-err-method* nil)
(defvar *op-term* nil)

;;; TRUTH, BOOL & IDENTICAL Module
;;;-----------------------------------------------------------------------------
(defvar *TRUTH-VALUE-module* 'void)
(defvar *TRUTH-module* 'void)
(defvar *BOOL-module* 'void)
(defvar *IDENTICAL-module* nil)
(defvar *EQL-module* nil)
(defvar *bootstrapping-bool* nil)
;;; basic operations in TRUTH & BOOL
;;;-----------------------------------------------------------------------------
(defvar *bool-true* 'void)
(defvar *bool-true-meth* 'void)
(defvar *bool-false* 'void)
(defvar *bool-false-meth* 'void)
(defvar *bool-and* 'void)
(defvar *bool-or* 'void)
(defvar *bool-not* 'void)
(defvar *sort-membership* 'void)
(defvar *bool-if* 'void)
(defvar *bool-imply* 'void)
(defvar *bool-xor* 'void)
(defvar *bool-equal* 'void)
(defvar *bool-match* 'void)
(defvar *beh-equal* 'void)
(defvar *bool-nonequal* 'void)
(defvar *beh-eq-pred* 'void)
(defvar *bool-and-also* 'void)
(defvar *bool-or-else* 'void)
(defvar *bool-iff* 'void)
(defvar *bool-cond-op* 'void)
(defvar *eql-op* 'void)
(defvar *m-and-op* nil)
(defvar *m-or-op* nil)

;;; RWL
;;;-----------------------------------------------------------------------------
(defvar *rwl-module* 'void)
(defvar *rwl-nat-star-sort* 'void)
(defvar *rwl-predicate* 'void)
(defvar *rwl-predicate2* 'void)

;;; search command related
(defvar .rwl-sch-context. nil)
(defvar .rwl-context-stack. nil)
(declaim (type fixnum .rwl-states-so-far.))
(defvar .rwl-states-so-far. 0)
(defvar *rwl-search-no-state-report* nil)

;;; basic operations in IDENTICAL.
;;;-----------------------------------------------------------------------------
(defvar *identical* 'void)
(defvar *nonidentical* 'void)

;;; constructors for record, object, attribute list.
;;;-----------------------------------------------------------------------------
(defvar *attribute-constructor* nil)
(defvar *attribute-list-constructor* nil)
(defvar *attribute-list-aux-variable* nil)
(defvar *object-reference-method* nil)
(defvar *object-constructor-method* nil)
(defvar *object-constructor-op* nil)
(defvar *record-constructor-method* nil)
(defvar *record-constructor-op* nil)
(defvar *void-object* nil)
(defvar *void-record* nil)

;;; ***************
;;; READER & PARSER_____________________________________________________________
;;; ***************

(declaim (special *parse-variables*
                  *fill-rc-attribute*
                  *lhs-attrid-vars*
                  *parsing-axiom-lhs*
                  *parse-lhs-attr-vars*)) ; binds variables during a parsing
                                        ; process. 
(declaim (special  *reader-schema-env*  ; current schema.
                   *reader-input*       ; current token sequence.
                   ))

(declaim (special *macroexpand*))       ; expand macro if t

(defvar *fill-rc-attribute* nil)        ; a flag, t if requires generalizing the
                                        ; pattern of record/object terms.

(defvar *parsing-axiom-lhs* nil)
(defvar *parse-lhs-attr-vars* nil)
(defvar *lhs-attrid-vars* nil)
;;;
(defparameter .lisp-start-symbol. #\#)
(defvar *parse-variables* nil)
(defconstant parser-min-precedence  0)
(defconstant parser-max-precedence 127)
(defvar *reader-schema-env* nil)
(defvar *reader-current-schema* nil)
(defvar *reader-current-context* nil)
(defvar *reader-starting-position* nil)
(defvar *builtin-ast-dict* (make-hash-table :test #'equal))
;;;
(defvar *parse-normalize* nil)
;;; if t, expand macros at parsing time.
;;;
(defvar *macroexpand* t)

;;; *********
;;; MISC VARS___________________________________________________________________
;;; *********

;;; *INCLUDE-BOOL* 
(defvar *include-bool* t)
(defvar *include-bool-save*)
;;; *INCLUDE-RWTL"
(defvar *include-rwl* t)
;;; *INCLUDE-FOPL*
(defvar *include-fopl* t)
;;;
(defvar *compile-lisp-rhs* t)
(defvar *running-with-tk* nil)
(defvar *sub-prompt* nil)
(defvar *no-prompt* nil)
(defvar *consider-object* nil)
(defvar *auto-reconstruct* nil)

;;; *SAVE-DEFINITION*
(defvar *save-definition* t)

;;; *MODMORPH-NEW-MODULE*
(declaim (special *modmorph-new-module*))
(defvar *modmorph-new-module* nil)

;;; TIMEZOE
(defvar *time-zone* -9)

;;; if true, top level command interpreter accept terms in current context
;;; and evaluate (reduce) it.
(defvar *allow-general-term-input* t)

;;; LIBRARY PATH
(defvar *chaos-libpath* nil)
;;;
(declaim (special *beh-proof-in-progress*))
(defvar *beh-proof-in-progress* nil)

;;; USER DEFINED BOOL
(defvar *user-bool* nil)

;;; TRAM
(defvar *tram-path* "tram")
(defvar *tram-options* "")
(defvar *tram-builtin-modules*)
(defvar *tram-bool-modules*)

;;; EXEC
(declaim (type fixnum *cexec-limit*))
(defvar *cexec-limit* most-positive-fixnum)
(declaim (type (or null (not null)) *cexec-trace* *cexec-normalize*))
(defvar *cexec-trace* nil)
(defvar *cexec-normalize* t)
(defvar *cexec-find-all-solutions* t)

;;; BUTILTIN
(defvar *compile-builtin-axiom* nil)
(defvar *bi-universal-operators* nil)

;;; OPEN/CLOSE WORLD -- not used.
;;; (declaim (special *closed-world*))
;; (defvar *closed-world* nil)

;;; ALLOW-UNIVERSAL-SORT
;;; t iff user refers to universal sorts,
;;; i.e., Universal, HUniversal, and Cosmos
;;;
(defvar *allow-universal-sort* nil)

;;; AUTOLOAD
(defvar *autoload-alist* nil)

;;; PARSER SETTINGS
(defvar *select-ambig-term* nil)

;;; if true accept system's congruency proof of operator =*=
(defvar *accept-system-proof* nil)

;;; find command control
(defvar *find-all-rules* nil)

;;; DEVELOPMENT MODE
(defvar *development-mode* nil)

;;; NO ID COMPLETION
(defvar *no-id-completion* nil)

;;; DEBUG FLAGS
(defvar *rewrite-debug* nil)
(defvar *on-term-hash-debug* nil)
(defvar *on-axiom-debug* nil)
(defvar *beh-debug* nil)
(defvar *gen-rule-debug* nil)
(defvar *on-change-debug* nil)
(defvar *on-operator-debug* nil)
(defvar *on-sort-debug* nil)
(defvar *on-trs-debug* nil)
(defvar *on-import-debug* nil)
(defvar *on-modexp-debug* nil)
(defvar *on-view-debug* nil)
(defvar *match-debug* nil)
(defvar *module-dep-debug* nil)
(defvar *term-debug* nil)
(defvar *on-parse-debug* nil)
(defvar *regularize-debug* nil)
(defvar *on-tram-debug* nil)
(defvar *mel-debug* nil)
(defvar *check-import-mode* nil)
(defvar *cexec-debug* nil)
(defvar *debug-meta* nil)
(defvar *debug-citp* nil)
(defvar *debug-print* nil)
(defvar *debug-bterm* nil)
;;;
;;; ** TO DO for other platforms
#+SBCL
(proclaim '(SB-EXT:DISABLE-PACKAGE-LOCKS 'SB-INT:TOPLEVEL-CATCHER))

(defvar *top-level-tag*
    #+KCL si::*quit-tag*
    #+CMU 'common-lisp::top-level-catcher
    #+EXCL 'top-level::top-level-break-loop
    #+(or LUCID :CCL) '(*quit-tag*)
    #+CLISP 'system::debug
    #+SBCL 'SB-INT:TOPLEVEL-CATCHER)

;;; EOF
