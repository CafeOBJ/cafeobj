;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|=============================================================================
                                  System:CHAOS
                                  Module:tools
                                File:compat.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;; CHECK COMPATIBILITY
;;;
(defun check-compatibility (&optional (module (get-context-module)))
  (unless *on-preparing-for-parsing*
    (prepare-for-parsing module))
  (with-in-module (module)
    (let ((rules (module-all-rules module))
          (non-decreasing-rules nil))
      ;; first, perform strong but light-weight check
      (dolist (rule rules)
        (unless (rule-is-builtin rule)
          (unless (sort<= (term-sort (rule-rhs rule))
                          (term-sort (rule-lhs rule)))
            (push rule non-decreasing-rules))))
      (unless non-decreasing-rules
        (return-from check-compatibility nil))
      ;; checks for each operations with non-decreasing rules.
      (let ((ops (module-all-operators module))
            (non-compat-rules nil))
        (dolist (rule non-decreasing-rules)
          (let ((lsort (term-sort (rule-lhs rule)))
                (rsort (term-sort (rule-rhs rule)))
                (e-methods nil))
            (dolist (opinfo ops)
              (let* ((op (opinfo-operator opinfo))
                     (name (operator-symbol op)))
                (dolist (method (cdr (opinfo-methods opinfo)))
                  (let ((pos-list nil)
                        (m-arity (method-arity method)))
                    (dotimes (x (length m-arity))
                      (when (sort<= lsort (nth x m-arity))
                        (push x pos-list)))
                    (when pos-list
                      (let ((new-arity (copy-list m-arity)))
                        (dolist (x pos-list)
                          (setf (nth x new-arity) rsort))
                        (unless (find-compat-method method name new-arity)
                          (push method e-methods))))))))
            (when e-methods
              (push (cons rule e-methods) non-compat-rules))
            ))
        non-compat-rules))))

(defun find-compat-method (method name arity)
  (when *on-debug*
    (format t "~%[find-compat-method] name = ~a, arity= " name)
    (print-sort-list arity))
  ;;
  (let ((len (length arity)))
    (dolist (opinfo (find-operators-in-module name len *current-module*) nil)
      (dolist (meth (opinfo-methods opinfo))
        (let ((m-ari (method-arity meth)))
          (when (and (not (eq method meth))
                     (= len (length m-ari))
                     (every #'(lambda (x y) (sort<= x y))
                            arity
                            (method-arity meth))
                     (not (method-is-error-method meth)))
            (when *on-debug*
              (format t "~%* found ")
              (print-chaos-object meth))
            (return-from find-compat-method meth)))))))

;;; EOF
