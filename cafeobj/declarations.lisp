;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                       File: declarations.lisp
==============================================================================|#
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ----------------------------------------
;;; register declarations keywords
;;; ----------------------------------------
(eval-when (:execute :load-toplevel)
  (clrhash *cafeobj-declarations*)
  
;;; 
;;; All the Declaration forms --------------------------------------------------------------
;;;

(define ("bsort")
    :type :inner-module
    :category :signature
    :parser process-bsort-declaration
    :evaluator eval-ast)

(define ("[")
    :type :inner-module
    :category :signature
    :parser process-sort-and-subsort-form
    :evaluator eval-ast)

(define ("hidden" "*")
    :type :inner-module
    :category :signature
    :parser process-hidden-sort-form
    :evaluator eval-ast)

(define ("op")
    :type :inner-module
    :category :signature 
    :parser process-operator-declaration-form
    :evaluator eval-ast)

(define ("ops")
    :type :inner-module
    :category :signature 
    :parser process-operators-declaration-form
    :evaluator eval-ast)

(define ("bop")
    :type :inner-module
    :category :signature
    :parser process-operator-declaration-form
    :evaluator eval-ast)

(define ("bops")
    :type :inner-module
    :category :signature 
    :parser process-boperators-declaration-form
    :evaluator eval-ast)

(define ("pred")
    :type :inner-module
    :category :signature
    :parser process-predicate-declaration-form
    :evaluator eval-ast)

(define ("dpred")
    :type :inner-module
    :category :signature 
    :parser process-predicate-declaration-form
    :evaluator eval-ast)
              
(define ("bpred")
    :type :inner-module
    :category :signature 
    :parser process-predicate-declaration-form
    :evaluator eval-ast)
              
(define ("dbpred")
    :type :inner-module
    :category :signature 
    :parser process-predicate-declaration-form
    :evaluator eval-ast)
              
(define ("rec" "record")
    :type :inner-module
    :category :signature 
    :parser process-record-declaration-form
    :evaluator eval-ast)

(define ("let")
    :type :inner-module
    :category :axiom
    :parser process-let-declaration-form
    :evaluator eval-ast)

(define ("#define")
    :type :inner-module
    :category :axiom
    :parser process-macro-declaration-form
    :evaluator eval-ast)

(define ("eq" "cq" "ceq" "rule" "rl" "crl" "crule" "trans" "ctrans" "trns" "ctrns"
	       "beq" "bceq" "brule" "brl" "bcrule" "bcrl" "btrans" "btrns"
	       "bctrans" "bctrns")
    :type :inner-module
    :category :axiom
    :parser process-axiom-form
    :evaluator eval-ast)

(define ("var" "vars")
    :type :inner-module
    :category :axiom
    :parser process-variable-declaration-form
    :evaluator eval-ast)
              
(define ("pvar" "pvars")
    :type :inner-module
    :category :axiom
    :parser process-pseud-variable-declaration-form
    :evaluator eval-ast)
              
(define ("fax" "bfax" "ax" "bax" "frm" "bfrm")
    :type :inner-module
    :category :axiom
    :parser pignose-process-fax-proc
    :evaluator eval-ast)

(define ("goal" "bgoal")
    :type :inner-module
    :category :axiom
    :parser pignose-process-goal-proc
    :evaluator eval-ast)
              
(define ("imports" "import")
    :type :inner-module
    :category :signature
    :parser parse-imports-form
    :evaluator eval-ast)

(define ("pr" "protecting" "ex" "extending" "us" "using" "inc" "including")
    :type :inner-module
    :category :import
    :parser process-importation-form
    :evaluator eval-ast)

(define ("--" "**")
    :type :inner-module
    :category :ignore
    :parser parse-decl-do-nothing
    :evaluator eval-decl-do-nothing)

(define ("-->")
    :type :inner-module
    :category :ignore
    :parser parse-dynamic-comment-1
    :evaluator eval-decl-do-nothing)

(define ("**>")
    :type :inner-module
    :category :ignore
    :parser parse-dynamic-comment-2
    :evaluator eval-decl-do-nothing)

(define ("ev" "lisp" "evq" "lispq")
    :type :inner-module
    :category :ignore
    :parser process-ev-lisp-form
    :evaluator eval-decl-do-nothing)

(define ("eval")
    :type :inner-module
    :category :misc
    :parser parse-eval-form
    :evaluator eval-ast)

(define ("sig" "signature")
    :type :inner-module
    :category :signature
    :parser process-signature
    :evaluator eval-ast)

(define ("axioms" "axiom" "axs")
    :type :inner-module
    :category :axiom
    :parser process-axioms-declaration
    :evaluator eval-ast)

(define (".")                    ; sole dots
    :type :inner-module
    :category :ignore
    :parser parse-decl-do-nothing
    :evaluator eval-decl-do-nothing)

;;;
)					; end eval-when
;;; EOF
