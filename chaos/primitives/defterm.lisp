;;;-*-Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
                               File: defterm.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; === DESCRIPTION ============================================================
;;; provides an aid for defining internal representations of objects.
;;; all of the categories are represented as symbols of keyword package.
;;;

;;; ******
;;; OBJECT :____________________________________________________________________
;;; ******
;;; The common structure of Chaos terms & semantics objects.

;;; 
;;; All instances of structures defined by defterm are called `Chaos Object's,
;;; which is a list whose first element is a keyword symbol indicating the type
;;; of the object.
;;;    (:type-name slots ....)
;;; Object types are further categorized into the following groups:
;;;    %object   : the term structure which represents a semantic object of
;;;                Chaos. visible language constructs are instantiated as an
;;;                instance of some type belonging to this category.
;;;    %int-object: internal data structure, does not appear at Chaos program.
;;;    %ast      : terms representing abstract syntax tree.
;;;
;;; NOTE: You must re-define the definition of %chaos-object if you want
;;; to change the internal representation of chaos terms.


;;; %CHAOS-OBJECT

(defstruct (%chaos-object (:print-function chaos-pr-object))
  (-type nil :type symbol)
  )

(defun chaos-pr-object (obj stream &rest ignore)
  (declare (type %chaos-object obj)
           (type stream stream)
           (ignore ignore))
  (format stream "#<~a : ~x>" (%chaos-object--type obj)
          (addr-of obj)))

(defstruct (%chaos-static-object #+gcl (:static t)
                                 )
  (-type nil :type symbol))

(defmacro object-type (_object_) `(%chaos-object--type ,_object_))

#+GCL
(defmacro chaos-object? (_object_) `(si::structurep ,_object_))

#-GCL
(defmacro chaos-object? (_object_) `(typep ,_object_ '%chaos-object))

(defmacro type-p-chaos (_object _type)
  (once-only (_object)
    ` (and (structure-p ,_object)
           (eq (object-type ,_object) ,_type))))

(defmacro object-category (_object) `(get (object-type ,_object) ':category))

(defmacro object-evaluator (_object) `(get (object-type ,_object) ':eval))

(defmacro object-printer (_object) `(get (object-type ,_object) ':print))

(defmacro object-visible-slots (_object)
  `(get (object-type ,_object) ':visible-slots))

(defmacro object-constructor (_object)
  ` (let ((key (object-type ,_object)))
      (and (fboundp key)
           (symbol-function key))))

;;;
;;; AST basic structure
;;;
(defstruct (%chaos-ast (:type list)) (-type nil))

(defmacro chaos-ast? (*object)
  (once-only (*object)
    ` (and (listp ,*object)
           (symbolp (car ,*object))
           (get (car ,*object) ':category))))

(defmacro ast-type (_ast_) `(car ,_ast_))

(defmacro ast-category (_ast_) `(get (car ,_ast_) ':category))

(defmacro ast-printer (_ast) `(get (ast-type ,_ast) ':print))

(defmacro ast-evaluator (_ast) `(get (ast-type ,_ast) ':eval))

;;; *******
;;; DEFTERM__________________
;;; *******
;;; defines term structure.

;;; ** NOTE ********************************************************************
;;; THIS MACRO ASSUMES THAT IT WILL BE CALLED ONLY AT THE TOP LEVEL.
;;; ****************************************************************************
;;;
(defun %make-keyword (symbol-or-string &optional (cat '%object))
  (declare (type (or symbol simple-string) symbol-or-string)
           (type symbol cat))
  (let ((nam nil))
    (if (member cat '(:ast :script :chaos-script) :test #'eq)
        (setq nam (concatenate 'string "%"
                               (the simple-string (string symbol-or-string))))
        (setq nam (string symbol-or-string)))
    (intern nam)))
  
(defmacro defterm (type (&optional super)
                   &key
                   (conc-name "")       ; conc-name
                   name                 ; name of the structure
                   visible              ; list of visible slots
                   hidden               ; list of invisible slots
                   eval                 ; evaluator
                   print                ; printer
                   category             ; internal group name
                   keyword              ; t if defining keyword
                   int-printer)
  (let ((optional? (memq '&optional visible))
        (rest? (memq '&rest visible)))
    (when (and optional? rest?)
      (error "you cannot specify &optional and &rest both at a time, sorry."))
    (when rest?
      (let ((len (length visible)))
        (declare (type fixnum len))
        (unless (eq '&rest (car (nthcdr (- len 2) visible)))
          (error "&rest must be the last slot specifier!"))
        ;; (setf rest-slot (car (last visible)))
        (setf visible (nconc (firstn visible (- len 2)) (cons '&optional
                                                              (last visible))))))
    (when super
      ;; NOTE:***********
      ;; (1) now does not check slot name confliction, use carefully if you use 
      ;;     super.
      ;; (2) &rest in super is not manpulated properly -> you cannot inherit
      ;;     super with &rest slot specifier.
      (unless (get super ':category)
        (error "No such super ~s" super)))
    (let* ((cat (if category category
                  (get super ':category)))
           (type-name (%make-keyword type cat))
           (name (if name name type))
           (slots (if super
                      (let ((osl (append visible hidden))
                            (ssl (get super ':chaos-slots))
                            (res nil))
                        (dolist (s osl)
                          (unless (memq s ssl)
                            (if (not (eq s '&optional))
                                (push s res))))
                        (append ssl (nreverse res)))
                    (nconc (remove '&optional visible) hidden)))
           (own-slots (if super
                          (let ((sss (get super :chaos-slots))
                                (os nil))
                            (dolist (s slots (nreverse os))
                              (unless (memq s sss)
                                (push s os))))
                        slots))
           (structure-conc-name (%make-keyword
                                 (concatenate 'string
                                   (the simple-string (string conc-name))
                                   (the simple-string (string name))
                                   "-")
                                 cat))
           (structure-constructor (%make-keyword
                                   (concatenate 'string
                                     (the simple-string
                                       (string conc-name))
                                     "MAKE-"
                                     (the simple-string
                                       (string name)))
                                   cat))
           (boa-constructor (%make-keyword (concatenate
                                               'string
                                             (the simple-string (string conc-name))
                                             (the simple-string (string name))
                                             "*")
                                           cat))
           (predicate-name (%make-keyword (concatenate 'string
                                            (the simple-string
                                              (string conc-name))
                                            "IS-"
                                            (the simple-string
                                              (string name)))
                                          cat))
           (int-predicate-name (%make-keyword (concatenate 'string
                                                (the simple-string
                                                  (string type-name))
                                                "-P"))))
      (if keyword
          `(eval-when (:execute :compile-toplevel :load-toplevel)
             (let ((*package *keyword-package*))
               (setf (get ',type-name ':category) ,cat)
               (defun ,type-name () ,type-name)
               ))
        `(eval-when (:execute :compile-toplevel :load-toplevel)
           (defparameter,type-name ',type-name)
           (setf (get ',type-name ':chaos-slots) ',slots)
           (setf (get ',type-name ':visible-slots) ',visible)
           (setf (get ',type-name ':category) ,cat)
           ;; the sutructure
           (defstruct (,type-name
                       (:conc-name ,structure-conc-name)
                       (:constructor ,structure-constructor)
                       (:constructor ,boa-constructor ,visible)
                       (:copier nil)
                       ,@(if (or (eq cat ':ast)
                                 (eq cat ':chaos-script))
                             (list '(:type list)
                                   `(:include %chaos-ast (-type ',type-name)))
                           (if (memq cat '(:static-object
                                           :static-int-object))
                               (list `(:include %chaos-static-object
                                                (-type ',type-name)))
                             (list `(:include ,(if super
                                                   super
                                                 '%chaos-object)
                                              (-type ',type-name))
                                   (if int-printer
                                       `(:print-function ,int-printer)
                                     '(:print-function chaos-pr-object))))))
             ,@own-slots)
           ;; predicate
           ,(case cat
              ((:ast :chaos-script)
               `(defun ,predicate-name (obj)
                  (and (chaos-ast? obj) (eq (ast-type obj) ',type-name))))
              (otherwise
               `(setf (symbol-function ',predicate-name)
                  (symbol-function ',int-predicate-name))))
           (setf (get ,type-name ':type-predicate)
             (symbol-function ',predicate-name))
           
           ;; evaluator
           (setf (get ',type-name ':eval) ',eval)
           
           ,(when (and eval (or (eq cat ':ast)
                                (eq cat ':chaos-script)))
              (let ((eval-mac (intern (concatenate
                                          'string
                                        "!"
                                        (the simple-string
                                          (string type-name))))))
                `(defmacro ,eval-mac (*__ast &optional *__context)
                   `(let ((*chaos-eval-context* ,*__context))
                      (eval-ast ,*__ast)))))
           ;; printer
           (setf (get ',type-name ':print) ',print)
           ;; type
           (deftype ,type-name () '(satisfies ,predicate-name)))))))

(defmacro defkey (name &key (category ':ast))
  `(defterm ,name () :keyword t :category ,category))

#-GCL (defun %is-chaos-term? (ast)
        (and (chaos-object? ast) (get (object-type ast) ':category)))
#+GCL
(si::define-inline-function %is-chaos-term? (ast)
  (and (not (stringp ast)) (chaos-object? ast) (get (object-type ast) ':category)))

;;; AST is defined by 'defterm'
;;;
(declaim (inline is-ast))
(defun is-ast (obj)
  (declare (optimize (speed 3) (safety 0)))
  (and (consp obj)
       (let ((cat (car obj)))
         (and (symbolp cat)
              (getf (symbol-plist cat) :category)))))

;;; EOF
