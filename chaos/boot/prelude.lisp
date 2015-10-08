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
                                 System: Chaos
                                Module: chaos
                               File: prelude.lisp
==============================================================================|#

;;;-----------------------------------------------------------------------------
;;; module LAST-TERM
;;;-----------------------------------------------------------------------------
(defvar *LAST-TERM-op-term* nil)
(defvar *LAST-TERM-eqn-rhs* nil)
(defun install-last-term ()
  (let* ((LAST-TERM (eval-modexp "LAST-TERM"))
         (opinfo nil))
    (with-in-module (last-term)
      (setq opinfo (find-operator '("last-term") 0 LAST-TERM))
      (setq *LAST-TERM-op-term* (opinfo-operator opinfo))
      (when *LAST-TERM-op-term*
        (let ((meth (opinfo-methods opinfo)))
          (when meth
            (let ((rules (method-rules-with-different-top (car meth))))
              (when rules
                (setf *LAST-TERM-eqn-rhs* (rule-rhs (car rules)))))
            ))))))

(defun set-last-term (term)
  (when *LAST-TERM-eqn-rhs*
    (term-replace *LAST-TERM-eqn-rhs* term)))

;;;-----------------------------------------------------------------------------
;;; module ERR
;;;-----------------------------------------------------------------------------
;;; (defvar *sort-error* 'none)
(defun is_Err_token (tok) (declare (ignore tok)) nil)
(defun create_Err (tok) (declare (ignore tok)) (error "Panic!") nil)
(defun print_Err (val)
  (princ "err!!") (print-chaos-object val))
(defun is_Err (val) (declare (ignore val)) t)
(defun install-err ()
  (setq *sort-error* 
        (find-sort-in (eval-modexp "ERR") '|Err|)))

                         
;;;-----------------------------------------------------------------------------
;;;  module BUILT-IN
;;;-----------------------------------------------------------------------------
(defvar obj-BUILTIN-keyword "built-in:")

(defstruct (bi-term (:print-function print$builtin)) val)

(defun print$builtin (x stream depth)
  (declare (ignore depth))
  (princ obj-BUILTIN-keyword stream)
  (princ " " stream)
  (let ((*standard-output* stream))
    (print-chaos-object (bi-term-val x))))

(defun is_Builtin_token (token)
  (typep token 'bi-term))
(defun create_Builtin (token)
  (bi-term-val token))
(defun print_Builtin (x)
  (princ obj-BUILTIN-keyword)
  (princ " ")
  (print-chaos-object x))
(defun is_Builtin (x)
  (declare (ignore x)) t)

(defun install_BUILTIN  ()
  (setq *sort_Builtin* 
        (find-sort-in (eval-modexp  "BUILT-IN") "Built-in")))

;;;-----------------------------------------------------------------------------
;;; module LISP
;;;-----------------------------------------------------------------------------
(defvar obj-lisp-keyword "lisp:")
(defstruct (lisp (:print-function print$lisp)) val)
(defun print$lisp (x stream depth)
  (declare (ignore depth))
  (princ obj-LISP-keyword stream) (princ " " stream)
  (prin1 (lisp-val x) stream))
(defvar *obj-LISP-eval-input* nil)
(defun is_Lisp_token (token) (typep token 'lisp))
(defun create_Lisp (token)
  (if *obj-LISP-eval-input*
      (eval (lisp-val token))
      (lisp-val token)))
(defun use (x) (throw 'direct-value x))
(defun print_Lisp (x) (princ obj-LISP-keyword) (princ " ") (prin1 x))
(defun is_Lisp (x) (declare (ignore x)) t)

;;;-----------------------------------------------------------------------------
;;; INSTALLING CafeOBJ PRELUDE
;;;-----------------------------------------------------------------------------
(defvar .re-install-proc.
    '(setup-truth-value
      setup-truth
      setup-bool
      setup-identical))

(defun re-install-cafeobj-prelude ()
  ;; (install-err)
  ;; (install_builtin)
  (dolist (fun .re-install-proc.)
    (and (fboundp fun) (funcall fun)))
  ;; (install-last-term)
  (setf *print-ignore-mods* nil)
  (setf *apply-ignore-modules* nil)
  (install-prelude)
  'done
  )

;;; INSTALL PRELUDE

(defun install-prelude ()
  (unless *print-ignore-mods*
    (setq *print-ignore-mods* *kernel-hard-wired-builtin-modules*))
  ;;
  (unless *apply-ignore-modules*
    (setq *apply-ignore-modules*
          (append *print-ignore-mods*
                  (mapcar #'eval-modexp
                          '("CHARACTER" "STRING" "OBJECT")))))
  )

;; EOF
