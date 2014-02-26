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

(define-command ("mod" "module" "module*" "mod*" "module!" "mod!" "sys:mod!")
  "declares module.~%module <Name> [<Parameters>] [<PrincipalSort>] { <ModuleBody> }."
  :toplevel-declaration
  process-module-declaration-form
  eval-ast)

(define-command ("view")
    "declares view.~%view <Name> { <Map> ... }"
  :topelevel-declaration
  process-view-declaration-form
  eval-ast)

(define-command ("check")
    "check current module's various properties.~
~%check regularity : checks whether module's signagure is regular or not"
  :checker
  parse-check-command
  eval-ast)

(define-command ("regularize")
    "destructively makes current module's signature to be regular by adding sorts and operators."
  :module
  parse-regularize-command
  eval-ast)

(define-command ("exec" "execute")
    "exec [in <Modexpr> :] <Term> . ~%Rewrite <Term> by '(c)trans' axioms of the module."
  :rewrite
  parse-exec-command
  eval-ast)

(define-command ("red" "reduce")
    "reduce [in <Modexpr> :] <Term> . ~%Rewrite <Term> by axioms of the module."
  :rewrite
  parse-reduce-command
  eval-ast)

(define-command ("exec!" "execute!")
    "exec! [in <Modexpr> :] <Term> . "
  :rewrite
  parse-exec+-command
  eval-ast)

(define-command ("bred" "breduce")
    ""
  :rewrite
  parse-bred-command
  eval-ast)

(define-command ("version")
    "prints version number of the system."
  :misc
  parse-version-command
  princ)

(define-command ("cbred")
    ""
  :rewrite
  parse-cbred-command
  eval-ast)

(define-command  ("stop")
    ""
  :rewrite
  parse-stop-at
  eval-ast)

(define-command ("parse")
    ""
  :inspect
  parse-parse-command
  eval-ast)

(define-command ("match" "unify")
    ""
  :inspect
  parse-match-command
  eval-ast)

(define-command ("lisp" "ev") 
    ""
  :system
  parse-eval-lisp
  cafeobj-eval-lisp-proc)

(define-command ("lispq" "evq")
    ""
  :system
  parse-eval-lisp
  cafeobj-eval-lisp-q-proc)

(define-command ("eval")
    ""
  :system
  parse-meta-eval
  eval-ast)

(define-command ("make")
    ""
  :toplevel-decl
  parse-make-command
  eval-ast)

(define-command  ("in" "input")
    ""
  :io
  parse-input-command
  cafeobj-eval-input-proc)

(define-command ("save")
    ""
  :io
  parse-save-command
  eval-ast)

(define-command ("restore")
    ""
  :io
  parse-restore-command
  eval-ast)

(define-command ("reset")
    ""
  :system-state
  parse-reset-command
  eval-ast)

(define-command ("full" "full-reset") 
    ""
  :system-state
  parse-full-reset-command
  eval-ast)

(define-command ("clean")
    ""
  :rewrite
  identity
  cafeobj-eval-clear-memo-proc)

(define-command  ("prelude")
    ""
  :library
  parse-prelude-command
  cafeobj-eval-prelude-proc)

(define-command ("let") 
    ""
  :toplevel-declaration
  process-let-declaration-form
  eval-ast)

(define-command ("--" "**")
    ""
  :toplevel-declaration
  parse-comment-command
  identity)

(define-command ("-->" "**>")
    ""
  :toplevel-declaration
  parse-comment-command
  eval-ast)

(define-command ("imports")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("ex" "extending")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("pr" "protecting")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("us" "using")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("inc" "including")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("[")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("*")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("bsort")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("op" "ops")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("bop" "bops")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("pred")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("bpred")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("dpred")		; only for pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("dbpred")		; only for pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("sig" "signature")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("axiom" "ax")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("axioms" "axs")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("ax")			; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("bax")			; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("goal")		; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("bgoal")		; pignose
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("#define")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)
  
(define-command ("var" "vars")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("pvar" "pvars")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("eq"  "ceq" "cq")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("beq" "bceq" "bcq")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("trans" "ctrans")
    ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)
    
(define-command ("trns" "ctrns")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("rule" "crule")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("rl" "crl")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("btrans" "bctrans")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("brule" "bcrule")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("btrns" "bctrns")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("brl" "bcrl")
        ""
  :module-element
  identity
  cafeobj-eval-module-element-proc)

(define-command ("open")
    ""
  :proof
  parse-open-command
  eval-ast)

(define-command ("close")
    ""
  :proof
  parse-close-command
  eval-ast)

(define-command ("start")
    ""
  :proof
  parse-start-command
  eval-ast)

(define-command ("apply")
    ""
  :proof
  parse-apply-command
  eval-ast)

(define-command  ("choose") 
    ""
  :proof
  parse-choose-command
  eval-ast)  

(define-command ("inspect")
    ""
  :proof
  parse-inspect-term-command
  eval-ast)

(define-command  ("find")
    ""
  :proof
  parse-find-command
  eval-ast)

(define-command  ("show" "sh")
    ""
  :inspect
  parse-show-command
  eval-ast)

(define-command  ("set")
    ""
  :switch
  parse-set-command
  eval-ast)

(define-command ("protect")
    ""
  :system-status
  parse-protect-command
  eval-ast)

(define-command ("unprotect") 
    ""
  :system-status
  parse-unprotect-command
  eval-ast)

(define-command ("select")
    ""
  :proof
  parse-show-command
  eval-ast)

(define-command ("describe" "desc")
    ""
  :inspect
  parse-show-command
  eval-ast)

(define-command  ("autoload")
    ""
  :library
  parse-autoload-command
  eval-ast)

(define-command  ("provide") 
    ""
  :library
  parse-provide-command
  eval-ast)

(define-command  ("require") 
    ""
  :library
  parse-require-command
  eval-ast)

(define-command ("??" "?")
    ""
  :help
  identity
  cafeobj-top-level-help)

(define-command  ("dribble")
    ""
  :misc
  parse-dribble-command
  eval-ast)

(define-command  ("pwd")
    ""
  :misc
  parse-pwd-command
  eval-ast)

(define-command  ("cd") 
    ""
  :misc
  parse-cd-command
  eval-ast)

(define-command ("pushd")
    ""
  :misc
  parse-pushd-command
  eval-ast)

(define-command  ("popd")
    ""
  :misc
  identity
  parse-pushd-command)

(define-command  ("dirs")
    ""
  :misc
  parse-dirs-command
  eval-ast)

(define-command ("ls")
    ""
  :misc
  parse-ls-command
  eval-ast)

(define-command ("!")
    ""
  :misc
  parse-shell-command
  eval-ast)

(define-command ("") 
    ""
  :misc
  identity
  cafeobj-eval-control-d)

(define-command ("cont" "continue")
    ""
  :rewrite
  parse-continue-command
  eval-ast)

(define-command ("look")
    ""
  :inspect
  parse-look-up-command
  eval-ast)

(define-command ("names" "name")
    ""
  :inspect
  parse-name-command
  eval-ast)

(define-command ("scase")
    ""
  :proof
  parse-case-command
  eval-ast)

(define-command ("sos" "passive")
    ""
  :proof
  pignose-parse-sos
  eval-ast)

(define-command ("db")
    ""
  :proof
  pignose-parse-db
  eval-ast)

(define-command  ("clause")
    ""
  :proof
  pignose-parse-clause
  eval-ast)

(define-command  ("list")
    ""
  :proof
  pignose-parse-list-command
  eval-ast)

(define-command ("flag")
    ""
  :proof
  pignose-parse-flag
  eval-ast)

(define-command  ("param")
    ""
  :proof
  pignose-parse-param
  eval-ast)

(define-command ("option")
    ""
  :proof
  pignose-parse-option
  eval-ast)

(define-command ("resolve")
    ""
  :proof
  pignose-parse-resolve
  eval-ast)

(define-command  ("demod")
    ""
  :proof
  pignose-parse-demod
  eval-ast)

(define-command ("save-option")
    ""
  :proof
  pignose-parse-save-option
  eval-ast)

(define-command ("sigmatch")
    ""
  :proof
  pignose-parse-sigmatch
  eval-ast)

(define-command  ("lex")
    ""
  :proof
  pignose-parse-lex
  eval-ast)

(define-command (".")
    ""
  :misc
  identity
  cafeobj-nop)

)
