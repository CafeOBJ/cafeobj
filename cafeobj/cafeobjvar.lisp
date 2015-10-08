;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
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
