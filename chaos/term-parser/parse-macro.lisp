;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
                                  System:Chaos
                           Module:term-parser.chaos
                            File: parse-macro.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defvar *debug-macro* nil)
(declaim (special *debug-macro-nest*))
(defvar *debug-marco-nest* 0)

(defun add-macro-to-module (module macro)
  (push macro (module-macros module)))

(defun setup-macro-rule (macro module)
  (add-macro-to-method macro
                       (term-head (macro-lhs macro))
                       (module-opinfo-table module)))

(defun add-macro-to-method (macro method
                            &optional (opinfo-table *current-opinfo-table*))
  (setf (method-macros method opinfo-table)
    (adjoin-macro macro (method-macros method opinfo-table))))

(defun adjoin-macro (macro ms)
  (do* ((lst ms (cdr lst))
        (r (car lst) (car lst)))
       ((null lst) (cons macro ms))
    (when (macro-is-similar? macro r)
      (let ((newlhs (macro-lhs macro))
            (oldlhs (macro-lhs r)))
        (when (and (not (term-is-variable? newlhs))
                   (not (term-is-variable? oldlhs))
                   (not (method= (term-method newlhs) (term-method oldlhs)))
                   (sort<= (term-sort oldlhs) (term-sort newlhs)))
          (rplaca lst r))
        (return-from adjoin-macro ms)))))

(defun macro-is-similar? (macro1 macro2)
  (and (term-is-congruent-2? (macro-lhs macro1)
                             (macro-lhs macro2))
       (term-is-congruent-2? (macro-rhs macro1)
                             (macro-rhs macro2))))

(defun expand-macro (term &optional (module (get-context-module)))
  (labels ((apply-macro-rule (macro term)
             (block the-end
               (multiple-value-bind (global-state subst no-match E-equal)
                   (first-match (macro-lhs macro) term)
                 (declare (ignore global-state e-equal))
                 (when no-match (return-from the-end nil))
                 (catch 'rule-failure
                   (term-replace term
                                 (substitute-image subst
                                                   (macro-rhs macro)))
                   (return-from the-end term))
                 nil)))
           ;;
           (substitute-image (sigma term)
             (declare (type list sigma)
                      (type term))
             (cond ((term-is-variable? term)
                    (let ((im (variable-image sigma term)))
                      (if im
                          im
                        term)))
                   ((term-is-builtin-constant? term) term)
                   ((term-is-lisp-form? term)
                    (multiple-value-bind (new success)
                        (funcall (lisp-form-function term) sigma)
                      (if success
                          new
                        (throw 'rule-failure nil))))
                   ((term-is-applform? term)
                    (let ((l-result nil))
                      (dolist (s-t (term-subterms term))
                        (push (substitute-image sigma s-t) l-result))
                      (make-term-with-sort-check (term-head term)
                                                 (nreverse l-result))))
                   )))
    ;;
    (unless (term-is-application-form? term)
      (return-from expand-macro term))
    ;;
    (with-in-module (module)
      (let ((*debug-macro-nest* (1+ *debug-marco-nest*)))
        (when *debug-macro*
          (format t "~%~D>[expand-macro]: " *debug-macro-nest*)
          (term-print term))
        (dolist (sub (term-subterms term))
          (expand-macro sub module))
        (update-lowest-parse term)
        (let ((top (term-head term)))
          (if (block the-end
                (dolist (rule (method-macros top))
                  (if (apply-macro-rule rule term)
                      (return-from the-end t))))
              (expand-macro term module))
          (update-lowest-parse term)
          (when *debug-macro*
            (format t "~%<~D " *debug-macro-nest*)
            (term-print term))
          term)
        ))))

;;; EOF
