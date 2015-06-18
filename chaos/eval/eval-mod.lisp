;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
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
                                  Module: eval
                              File: eval-mod.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ***************************
;;; TOP LEVEL MODEXPR EVALUATOR
;;; ***************************

;;; MODEXP-TOP-LEVEL-EVAL pre-modexp
;;; given a module expression no yet parsed, parses it, then
;;; evaluate the modexp.
;;;
(defun modexp-top-level-eval (modexp)
  (let ((meparse (parse-modexp modexp)))
    (eval-modexp-top (normalize-modexp meparse))))

;;; EVAL-MOD
;;; similar to MODEXP-TOP-LEVEL-EVAL.
;;; specially handles the modexp "%" (opening module).
;;;
(defun eval-mod (toks &optional (change-context *auto-context-change*))
  (if (null toks)
      (or (get-context-module)
          (with-output-chaos-error ('no-context)
            (princ "no selected(current) module.")))
      (if (equal '("%") toks)
          (if *open-module*
              (let ((mod (find-module-in-env (normalize-modexp "%"))))
                (unless mod
                  (with-output-panic-message ()
                    (princ "could not find % module!!!!")
                    (chaos-error 'panic)))
                (when change-context
                  (change-context (get-context-module) mod))
                mod)
              (with-output-chaos-warning ()
                (princ "no module is opening.")
                (chaos-error 'no-open-module)))
          (let ((val (modexp-top-level-eval toks)))
            (if (modexp-is-error val)
                (if (and (null (cdr toks))
                         (<= 4 (length (car toks)))
                         (equal "MOD" (subseq (car toks) 0 3)))
                    (let ((val (read-from-string (subseq (car toks) 3))))
                      (if (integerp val)
                          (let ((nmod (print-nth-mod val))) ;;; !!!
                            (when change-context
                              (change-context (get-context-module) nmod))
                            nmod)
                          (with-output-chaos-error ('no-such-module)
                            (format t "could not evaluate the modexp ~a" toks))))
                    (with-output-chaos-error ('no-such-module)
                      (format t "undefined module? ~a" toks)
                      ))
                (progn
                  (when change-context
                    (change-context (get-context-module) val))
                  val))))))

;;; what to do with this one?

(defun print-nth-mod (&rest ignore)
  (declare (ignore ignore))
  nil)

;;; EVAL-MOD-EXT
;;; evaluate modexp not yet parsed with some extension:
;;; - handles "sub"     --- submodule
;;;           "param"   --- parameter
;;;   
(defun eval-mod-ext (toks &optional
                          (change-context *auto-context-change* force?))
  (when (equal toks ".")
    (setq toks nil))
  (when (and (listp toks)
             (equal (car (last toks)) "."))
    (setq toks (butlast toks)))
  (let ((it (car toks)))
    (when (equal it ".")
      (setq it nil)
      (setq toks nil))
    (cond ((and (equal "sub" it)
                (cadr toks)
                (parse-integer (cadr toks) :junk-allowed t))
           (let* ((no (read-from-string (cadr toks)))
                  (mod (eval-mod-ext (cddr toks) nil))
                  (sub (nth-sub (1- no) mod)))
             (if sub
                 (when change-context
                   (change-context (get-context-module) sub))
                 (progn (princ "** Waring : No such sub-module") (terpri) nil))))
          ((and (equal "param" it)
                (cadr toks)
                (parse-integer (cadr toks) :junk-allowed t))
           (let* ((no (read-from-string (cadr toks)))
                  (mod (eval-mod-ext (cddr toks) nil))
                  (params (module-parameters mod))
                  (param (nth (1- no) params)))
             (if param
                 (when change-context
                   (change-context (get-context-module) (cdr param)))
                 (with-output-chaos-error ('no-such-parameter)
                   (princ "No such parameter")
                   ))))
          ((and (null toks) change-context force?)
           (when (get-context-module)
             (change-context (get-context-module) nil)))
          (t (eval-mod toks change-context)))))

;;; EOF
