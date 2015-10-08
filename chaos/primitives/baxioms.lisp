;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
                               Module: primitives
                               File: baxiom.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************************************************************************
;;; STRUCTURES & BASION OPERATORS ON REWRITE RULES and AXIOMS ******************
;;; ****************************************************************************

;;;=============================================================================
;;;                            AXIOM/REWRITE RULE
;;;=============================================================================

;;; ************
;;; REWRITE RULE : internal use only
;;; ************

(defstruct (rewrite-rule (:include object (-type 'rewreite-rule))
                         (:copier nil)
                         (:constructor make-rewrite-rule)
                         (:constructor
                          rewrite-rule* (type lhs rhs condition behavioural
                                              id-condition first-match-method
                                              next-match-method labels
                                              trace-flag
                                              ))
                         (:print-function print-rule-object))
  (type nil :type symbol)               ; type, either ':equation or ':rule
  (lhs nil :type (or null term))
  (rhs nil :type (or null term))
  (condition nil :type (or null term))
  (behavioural nil :type (or null t))
  (id-condition nil :type list)
  (first-match-method nil :type symbol)
  (next-match-method nil :type symbol)
  (labels nil :type list)
  (trace-flag nil :type (or null t))
  (need-copy nil :type (or null t))
  (non-exec nil :type (or null t))
  (meta-and-or nil :type (or null t))   ; :m-and or :m-or
  )

(eval-when (:execute :load-toplevel)
  (setf (get 'rewrite-rule :type-predicate)
        (symbol-function 'rewrite-rule-p))
  (setf (symbol-function 'is-rewrite-rule)
        (symbol-function 'rewrite-rule-p))
  (setf (get 'rewrite-rule :print) 'print-rule-internal))

(defun print-rule-object (obj stream &rest ignore)
  (declare (ignore ignore))
  (if *current-module*
      (progn
        (format stream ":rule[~S: " (addr-of obj))
        (print-axiom-brief obj stream)
        (format stream "]"))
    (format stream ":rule[~a]" (rewrite-rule-type obj))))

;;;
(defmacro rule-type (_rule) `(rewrite-rule-type ,_rule))
(defmacro rule-is-rule (_rule) `(eq (rewrite-rule-type ,_rule) ':rule))
(defmacro rule-is-equation (_rule) `(eq (rewrite-rule-type ,_rule) ':equation))
(defmacro rule-lhs (_rule) `(rewrite-rule-lhs ,_rule))
(defmacro rule-rhs (_rule) `(rewrite-rule-rhs ,_rule))
(defmacro rule-condition (_rule) `(rewrite-rule-condition ,_rule))
(defmacro rule-id-condition (_rule) `(rewrite-rule-id-condition ,_rule))
(defmacro rule-first-match-method (_rule) `(rewrite-rule-first-match-method
                                            ,_rule))
(defmacro rule-next-match-method (_rule) `(rewrite-rule-next-match-method
                                              ,_rule)) 
(defmacro rule-labels (_rule) `(rewrite-rule-labels ,_rule))
(defmacro rule-is-behavioural (_rule) `(rewrite-rule-behavioural ,_rule))
(defmacro rule-trace-flag (_rule) `(rewrite-rule-trace-flag ,_rule))
(defmacro rule-need-copy (_rule) `(rewrite-rule-need-copy ,_rule))
(defmacro rule-non-exec (_rule) `(rewrite-rule-non-exec ,_rule))
(defmacro rule-meta-and-or (_rule) `(rewrite-rule-meta-and-or ,_rule))

;;; Extended rewrite rule
;;;

(defstruct (ex-rewrite-rule (:include rewrite-rule (-type 'ex-rewrite-rule))
                            (:copier nil)
                            (:print-function print-rule-object)
                            (:constructor make-ex-rewrite-rule)
                            (:constructor
                             ex-rewrite-rule* (type lhs rhs condition
                                                    behavioural id-condition
                                                    first-match-method
                                                    next-match-method
                                                    extensions)))
  (extensions nil :type list))

(eval-when (:execute :load-toplevel)
  (setf (get 'ex-rewrite-rule :type-predicate)
        (symbol-function 'ex-rewrite-rule-p))
  (setf (symbol-function 'is-ex-rewrite-rule)
        (symbol-function 'ex-rewrite-rule-p))
  (setf (get 'ex-rewrite-rule :print)
        'print-rule-internal))

(defmacro rule-extensions (_rule) `(ex-rewrite-rule-extensions ,_rule))

;;; Predicates
(defmacro rewirte-rule-p (_*_obj)
  (once-only (_*_obj)
    `(and (chaos-object? ,_*_obj) 
          (memq (object-type ,_*_obj) '(rewrite-rule ex-rewrite-rule)))))

(defmacro is-rewrite-rule? (*--obj)     ; synonym
  `(rewrite-rule-p ,*--obj))

;;; CONSTRUCTOR
;;;
(defmacro create-rewrite-rule (type lhs rhs condition behavioural
                               id-condition first-match-method
                               next-match-method extensions
                               &optional (meta-and-or nil))
  ` (create-ex-rewrite-rule ,type
                            ,lhs
                            ,rhs
                            ,condition
                            ,behavioural
                            ,id-condition
                            ,first-match-method
                            ,next-match-method
                            ,extensions
                            ,meta-and-or))
  
;;; ***** 
;;; AXIOM________________________________________________________________________
;;; *****
;;; definition of axiom structure.
;;;
(defstruct (axiom (:include rewrite-rule (-type 'axiom))
                  (:copier nil)
                  (:constructor make-axiom)
                  (:constructor
                   axiom* (type lhs rhs condition behavioural))
                  (:print-function print-axiom-object))
  (kind nil :type symbol)               ; internaly categorized kind name of an
  )

(eval-when (:execute :load-toplevel)
  (setf (get 'axiom :type-predicate) (symbol-function 'axiom-p))
  (setf (get 'axiom :print) 'print-axiom-brief)
  (setf (symbol-function 'is-axiom) (symbol-function 'axiom-p))
  )

(defun print-axiom-object (obj stream &rest ignore)
  (declare (ignore ignore))
  (if *current-module*
      (with-in-module (*current-module*)
        (print-axiom-brief obj stream nil nil t))
    (format stream ":axiom[~S]" (addr-of obj))))

;;; Type predicate -------------------------------------------------------------

(defmacro is-axiom? (*--obj) `(is-axiom ,*--obj))
    
;;; Primitive structure accessors ----------------------------------------------

(defmacro axiom-is-behavioural (_a) `(axiom-behavioural ,_a))

(defmacro axiom-is-for-cr (_a) `(object-info ,_a :cr))

(defmacro axiom-contains-match-op (_a) `(object-info ,_a :match-op))

(defun axiom-extensions (_x &optional (_ext-rule-table
                                       *current-ext-rule-table*))
  (declare (type axiom _x)
           (type symbol _ext-rule-table)
           (values list))
  (cdr (assq _x (get _ext-rule-table :ext-rules))))

(defsetf axiom-extensions (_x &optional (_ext-rule-table
                                         '*current-ext-rule-table*))
    (_value)
  ` (let* ((axiom ,_x)
           (rule-table (get ,_ext-rule-table :ext-rules))
           (pre (assq axiom rule-table))
           (extensions ,_value))
      (if pre
          (setf (cdr pre) extensions)
          (if rule-table
              (setf (get ,_ext-rule-table :ext-rules)
                    (nconc rule-table (list (cons axiom extensions))))
              (setf (get ,_ext-rule-table :ext-rules)
                    (list (cons axiom extensions)))))
      extensions))
    
(defmacro axiom-ac-extension (_x &optional
                                 (_ext-rule-table '*current-ext-rule-table*))
  `(axiom-extensions ,_x ,_ext-rule-table))

(defmacro axiom-a-extensions (_x &optional
                                 (_ext-rule-table '*current-ext-rule-table*))
  `(axiom-extensions ,_x ,_ext-rule-table))
  
(defmacro !axiom-ac-extension (_ax &optional
                               (_ext-rule-table '*current-ext-rule-table*))
  `(axiom-extensions ,_ax ,_ext-rule-table))

(defmacro !axiom-a-extensions (_ax &optional
                               (_ext-rule-table '*current-ext-rule-table*))
  `(axiom-extensions ,_ax ,_ext-rule-table))

;;; the basic constructor
;;; create-axiom
;;;
(defun create-axiom (lhs
                     rhs
                     condition
                     type
                     behavioural
                     id-condition
                     extensions
                     kind
                     first-match-method
                     next-match-method
                     labels
                     &optional (meta-and-or nil))
  (declare (type term lhs rhs condition)
           (type (or null t) behavioural)
           (type symbol type kind first-match-method next-match-method)
           (type list id-condition extensions labels)
           (values axiom))
  (let ((r (axiom* type lhs rhs condition behavioural)))
    (setf (axiom-id-condition r) id-condition)
    (when extensions
      (setf (axiom-extensions r) extensions))
    (setf (axiom-kind r) kind)
    (setf (axiom-first-match-method r) first-match-method)
    (setf (axiom-next-match-method r) next-match-method)
    (setf (axiom-labels r) labels)
    (setf (axiom-meta-and-or r) meta-and-or)
    (set-object-context-module r)
    r))

(defmacro rule-is-builtin (_rule_)
  ` (term$is-lisp-code? (term-body (rule-rhs ,_rule_))))

;;; AXIOM-CONTAINS-ERROR-METHOD? : Axiom -> Bool
;;; retrurns true iff the axiom contains terms with error-method as top.
;;;
(defun axiom-contains-error-method? (e)
  (declare (type axiom e)
           (values (or null t)))
  (macrolet ((error-method-term? (term)
               (once-only (term)
                ` (and (term-is-application-form? (the term ,term))
                       (method-is-error-method (the method (term-head ,term)))))))
    (or (error-method-term? (axiom-lhs e))
        (error-method-term? (axiom-rhs e))
        (error-method-term? (axiom-condition e)))))

;;;=============================================================================
;;;                                 THEOREM
;;;=============================================================================

;;;********
;;; Theorem
;;;********

;;; *NOT YET*

;;; EOF
