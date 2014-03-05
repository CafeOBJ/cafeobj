;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                         File: defcommand.lisp
==============================================================================|#
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ----------------------------------------
;;; register commands & declaration keywords
;;; ----------------------------------------
(eval-when (:execute :load-toplevel)

  (clrhash *cafeobj-commands*)
  (clrhash *cafeobj-declarations*)
  
;;;
;;; commands which can apper at top-level --------------------------------------
;;;  

(defcom ("mod" "module" "module*" "mod*" "module!" "mod!" "sys:mod!")
  "declares module.~%module <Name> [<Parameters>] [<PrincipalSort>] { <ModuleBody> }."
  :toplevel-declaration
  process-module-declaration-form
  eval-ast)

(defcom ("view")
    "declares view.~%view <Name> { <Map> ... }"
  :topelevel-declaration
  process-view-declaration-form
  eval-ast)

(defcom ("check")
    "check current module's various properties.~
~%check regularity : checks whether module's signagure is regular or not"
  :checker
  parse-check-command
  eval-ast)

(defcom ("regularize")
    "destructively makes current module's signature to be regular by adding sorts and operators."
  :module
  parse-regularize-command
  eval-ast)

(defcom ("exec" "execute")
    "exec [in <Modexpr> :] <Term> . ~%Rewrite <Term> by '(c)trans' axioms of the module."
  :rewrite
  parse-exec-command
  eval-ast)

(defcom ("red" "reduce")
    "reduce [in <Modexpr> :] <Term> . ~%Rewrite <Term> by axioms of the module."
  :rewrite
  parse-reduce-command
  eval-ast)

(defcom ("exec!" "execute!")
    "exec! [in <Modexpr> :] <Term> . "
  :rewrite
  parse-exec+-command
  eval-ast)

(defcom ("bred" "breduce")
    ""
  :rewrite
  parse-bred-command
  eval-ast)

(defcom ("version")
    "prints version number of the system."
  :misc
  parse-version-command
  princ)

(defcom ("cbred")
    ""
  :rewrite
  parse-cbred-command
  eval-ast)

(defcom  ("stop")
    ""
  :rewrite
  parse-stop-at
  eval-ast)

(defcom ("parse")
    ""
  :inspect
  parse-parse-command
  eval-ast)

(defcom ("match" "unify")
    ""
  :inspect
  parse-match-command
  eval-ast)

(defcom ("lisp" "ev") 
    ""
  :system
  parse-eval-lisp
  cafeobj-eval-lisp-proc)

(defcom ("lispq" "evq")
    ""
  :system
  parse-eval-lisp
  cafeobj-eval-lisp-q-proc)

;;; (defcom ("eval")
;;;    ""
;;;  :system
;;;  parse-meta-eval
;;;  eval-ast)

(defcom ("make")
    ""
  :toplevel-decl
  parse-make-command
  eval-ast)

(defcom  ("in" "input")
    ""
  :io
  parse-input-command
  cafeobj-eval-input-proc)

(defcom ("save")
    ""
  :io
  parse-save-command
  eval-ast)

(defcom ("restore")
    ""
  :io
  parse-restore-command
  eval-ast)

(defcom ("reset")
    ""
  :system-state
  parse-reset-command
  eval-ast)

(defcom ("full" "full-reset") 
    ""
  :system-state
  parse-full-reset-command
  eval-ast)

(defcom ("clean")
    ""
  :rewrite
  identity
  cafeobj-eval-clear-memo-proc)

(defcom  ("prelude")
    ""
  :library
  parse-prelude-command
  cafeobj-eval-prelude-proc)

(defcom ("let") 
    ""
  :toplevel-declaration
  process-let-declaration-form
  eval-ast)

(defcom ("--" "**")
    ""
  :toplevel-declaration
  parse-comment-command
  identity)

(defcom ("-->" "**>")
    ""
  :toplevel-declaration
  parse-comment-command
  eval-ast)

(defcom ("imports")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("ex" "extending")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("pr" "protecting")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("us" "using")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("inc" "including")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("[")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("*")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("bsort")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("op" "ops")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("bop" "bops")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("pred")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("bpred")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("dpred")		; only for pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("dbpred")		; only for pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("sig" "signature")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("axiom" "ax")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("axioms" "axs")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("ax")			; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("bax")			; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("goal")		; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("bgoal")		; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("#define")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)
  
(defcom ("var" "vars")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("pvar" "pvars")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("eq"  "ceq" "cq")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("beq" "bceq" "bcq")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("trans" "ctrans")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)
    
(defcom ("trns" "ctrns")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("rule" "crule")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("rl" "crl")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("btrans" "bctrans")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("brule" "bcrule")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("btrns" "bctrns")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("brl" "bcrl")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(defcom ("open")
    ""
  :proof
  parse-open-command
  eval-ast)

(defcom ("close")
    ""
  :proof
  parse-close-command
  eval-ast)

(defcom ("start")
    ""
  :proof
  parse-start-command
  eval-ast)

(defcom ("apply")
    ""
  :proof
  parse-apply-command
  eval-ast)

(defcom  ("choose") 
    ""
  :proof
  parse-choose-command
  eval-ast)  

(defcom ("inspect")
    ""
  :proof
  parse-inspect-term-command
  eval-ast)

(defcom  ("find")
    ""
  :proof
  parse-find-command
  eval-ast)

(defcom  ("show" "sh")
    ""
  :inspect
  parse-show-command
  eval-ast)

(defcom  ("set")
    ""
  :switch
  parse-set-command
  eval-ast)

(defcom ("protect")
    ""
  :system-status
  parse-protect-command
  eval-ast)

(defcom ("unprotect") 
    ""
  :system-status
  parse-unprotect-command
  eval-ast)

(defcom ("select")
    ""
  :proof
  parse-show-command
  eval-ast)

(defcom ("describe" "desc")
    ""
  :inspect
  parse-show-command
  eval-ast)

(defcom  ("autoload")
    ""
  :library
  parse-autoload-command
  eval-ast)

(defcom  ("provide") 
    ""
  :library
  parse-provide-command
  eval-ast)

(defcom  ("require") 
    ""
  :library
  parse-require-command
  eval-ast)

(defcom ("??" "?")
    ""
  :help
  identity
  cafeobj-top-level-help)

(defcom  ("dribble")
    ""
  :misc
  parse-dribble-command
  eval-ast)

(defcom  ("pwd")
    ""
  :misc
  parse-pwd-command
  eval-ast)

(defcom  ("cd") 
    ""
  :misc
  parse-cd-command
  eval-ast)

(defcom ("pushd")
    ""
  :misc
  parse-pushd-command
  eval-ast)

(defcom  ("popd")
    ""
  :misc
  identity
  parse-pushd-command)

(defcom  ("dirs")
    ""
  :misc
  parse-dirs-command
  eval-ast)

(defcom ("ls")
    ""
  :misc
  parse-ls-command
  eval-ast)

(defcom ("!")
    ""
  :misc
  parse-shell-command
  eval-ast)

(defcom ("") 
    ""
  :misc
  identity
  cafeobj-eval-control-d)

(defcom ("cont" "continue")
    ""
  :rewrite
  parse-continue-command
  eval-ast)

(defcom ("look")
    ""
  :inspect
  parse-look-up-command
  eval-ast)

(defcom ("names" "name")
    ""
  :inspect
  parse-name-command
  eval-ast)

(defcom ("scase")
    ""
  :proof
  parse-case-command
  eval-ast)

(defcom ("sos" "passive")
    ""
  :proof
  pignose-parse-sos
  eval-ast)

(defcom ("db")
    ""
  :proof
  pignose-parse-db
  eval-ast)

(defcom  ("clause")
    ""
  :proof
  pignose-parse-clause
  eval-ast)

(defcom  ("list")
    ""
  :proof
  pignose-parse-list-command
  eval-ast)

(defcom ("flag")
    ""
  :proof
  pignose-parse-flag
  eval-ast)

(defcom  ("param")
    ""
  :proof
  pignose-parse-param
  eval-ast)

(defcom ("option")
    ""
  :proof
  pignose-parse-option
  eval-ast)

(defcom ("resolve")
    ""
  :proof
  pignose-parse-resolve
  eval-ast)

(defcom  ("demod")
    ""
  :proof
  pignose-parse-demod
  eval-ast)

(defcom ("save-option")
    ""
  :proof
  pignose-parse-save-option
  eval-ast)

(defcom ("sigmatch")
    ""
  :proof
  pignose-parse-sigmatch
  eval-ast)

(defcom  ("lex")
    ""
  :proof
  pignose-parse-lex
  eval-ast)

(defcom (".")
    ""
  :misc
  identity
  cafeobj-nop)

;;; Declaration forms
;;;
(defdecl ("bsort")
    ""
  :sig
  process-bsort-declaration
  eval-ast)

(defdecl ("[")
    ""
  :sig
  process-sort-and-subsort-form
  eval-ast)

(defdecl ("hidden" "*")
    ""
  :sig
  process-hidden-sort-form
  eval-ast)

(defdecl ("op")
    ""
  :sig 
  process-operator-declaration-form
  eval-ast)

(defdecl ("ops")
  ""
  :sig 
  process-operators-declaration-form
  eval-ast)

(defdecl ("bop")
    ""
  :sig process-operator-declaration-form
  eval-ast)

(defdecl ("bops")
    ""
  :sig 
  process-boperators-declaration-form
  eval-ast)

(defdecl ("pred")
    ""
  :sig
  process-predicate-declaration-form
  eval-ast)

(defdecl ("dpred")
    ""
  :sig 
  process-predicate-declaration-form
  eval-ast)
              
(defdecl ("bpred")
    ""
  :sig 
  process-predicate-declaration-form
  eval-ast)
              
(defdecl ("dbpred")
    ""
  :sig 
  process-predicate-declaration-form
  eval-ast)
              
;;;(defdecl ("opattr" "attr" "attrs")
;;;    ""
;;;  :sig
;;;  process-opattr-declaration-form
;;;  eval-ast)
              
(defdecl ("rec" "record")
    ""
  :sig 
  process-record-declaration-form
  eval-ast)

;;(defdecl ("cls" "class")
;;    ""
;;  :sig process-class-declaration-form
;;  eval-ast)

(defdecl ("let")
    ""
  :ax 
  process-let-declaration-form
  eval-ast)

(defdecl ("#define")
    ""
  :ax
  process-macro-declaration-form
  eval-ast)

(defdecl ("eq" "cq" "ceq" "rule" "rl" "crl" "crule" "trans" "ctrans" "trns" "ctrns"
	       "beq" "bceq" "brule" "brl" "bcrule" "bcrl" "btrans" "btrns"
	       "bctrans" "bctrns")
    ""
  :ax
  process-axiom-form
  eval-ast)

(defdecl ("var" "vars")
    ""
  :ax
  process-variable-declaration-form
  eval-ast)
              
(defdecl ("pvar" "pvars")
    ""
  :ax
  process-pseud-variable-declaration-form
  eval-ast)
              
(defdecl ("fax" "bfax" "ax" "bax" "frm" "bfrm")
    ""
  :ax
  pignose-process-fax-proc
  eval-ast)

(defdecl ("goal" "bgoal")
    ""
  :ax
  pignose-process-goal-proc
  eval-ast)
              
(defdecl ("imports" "import")
    ""
  :sig
  parse-imports-form
  eval-ast)

(defdecl ("pr" "protecting" "ex" "extending" "us" "using" "inc" "including")
    ""
  :sig 
  process-importation-form
  eval-ast)

(defdecl ("--" "**")
    ""
  :ignore
  parse-decl-do-nothing
  eval-decl-do-nothing)

(defdecl ("-->")
    ""
  :ignore
  parse-dynamic-comment-1
  eval-decl-do-nothing)

(defdecl ("**>")
    ""
  :ignore
  parse-dynamic-comment-2
  eval-decl-do-nothing)

(defdecl ("ev" "lisp" "evq" "lispq")
    ""
  :ignore
  process-ev-lisp-form
  eval-decl-do-nothing)

(defdecl ("eval")
    ""
  :misc
  parse-eval-form
  eval-ast)

(defdecl ("sig" "signature")
    ""
  :sig
  process-signature
  eval-ast)

(defdecl ("axioms" "axiom" "axs")
    ""
  :ax 
  process-axioms-declaration
  eval-ast)

(defdecl (".")                    ; sole dots
    ""
  :ignore
  parse-decl-do-nothing
  eval-decl-do-nothing)


)
