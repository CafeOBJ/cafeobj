;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cafeobjvar.lisp,v 1.2 2007-01-11 10:41:31 sawada Exp $
(in-package :chaos)
#|==============================================================================
                             System: CHAOS
                            Module: cafeobj
                          File: cafeobjvar.lisp
==============================================================================|#

;;; DESCRIPTION ================================================================
;;; CafeOBJ interpreter global variables and parameters.
;;;

(defvar *cafeobj-batch* nil)
(defvar *cafeobj-no-banner* nil)
;; (defvar *cafeobj-input-quiet* nil)
;; (defvar $)
(defvar *cafeobj-verbose* nil)
(defvar *prompt* 'system)
(defvar *cafeobj-initial-load-files* nil)
(defvar *cafeobj-initial-prelude-file* nil)
(defvar *cafeobj-secondary-prelude-file* nil)
(defvar *cafeobj-load-init-file* t)
;;; (defvar *cafeobj-load-path* nil)
;;; (defvar *cafeobj-standard-prelude-path* nil)
(defvar *cafeobj-secondary-prelude-path* nil)

(defvar *cafeobj-install-dir* nil)      ; must be set at make time.

;; (defvar -cafeobj-load-time- nil)        ; set by save-cafeobj.

(defvar *cafeobj-schemas* nil)
(defvar *cafeobj-print-errors* t)


;;; keywords of CafeOBJ module elements.

(defparameter *cafeobj-mod-elts*
    '("imports"
      "ex" "extending"
      "pr" "protecting"
      "us" "using"
      "inc" "including" 
      "["
      ;; "hidden"
      "*"
      "*record"
      "*class"
      "bsort"
      "op" "ops"
      "bop" "bops"
      "pred"
      "bpred"
      "dpred"                           ; only for pignose
      "dbpred"                          ; ditto
      "sig" "signature"
      "axiom" "ax"
      "axioms" "axs"
      #+:bigpink
      "ax"
      #+:bigpink
      "bax"
      #+:bigpink
      "goal"
      #+:bigpink
      "bgoal"
      "rec" "record"
      "class"
      "let"
      "#define"
      "var" "vars"
      "pvar" "pvars"
      "eq"  "ceq" "cq"
      "beq" "bceq" "bcq"
      "trans" "ctrans"
      "trns" "ctrns"
      "rule" "crule"
      "rl" "crl"
      "btrans" "bctrans"
      "brule" "bcrule"
      "btrns" "bctrns"
      "brl" "bcrl"
      ))

;;; EOF
