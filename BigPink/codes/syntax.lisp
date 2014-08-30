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
;;;
(in-package :chaos)
#|=============================================================================
			    System:Chaos
			  Module:BigPink
			   File:syntax.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;; INSTALL-FOPL-SENTENCE
;;;
(defun install-fopl-sentence (mod-name
			      &key (sentence-sort "FoplSentence")
				   (vardecl-sort "VarDeclList")
				   (var-decl-list '("_" "," "_"))
				   (forall '("\\A" "[" "_" "]" "_"))
				   (exists  '("\\E" "[" "_" "]" "_"))
				   (and '("_" "&" "_"))
				   (or '("_" "|" "_"))
				   (imply '("_" "->" "_"))
				   (iff '("_" "<->" "_"))
				   (not '("~" "_"))
				   (eq nil)
				   (beq nil))
  (let ((fopl-sentence-module (eval-modexp mod-name)))
    (cond ((and fopl-sentence-module (not (modexp-is-error fopl-sentence-module)))
	   (setq *fopl-sentence-module* fopl-sentence-module)
	   (setf (module-type *fopl-sentence-module*) :system)
	   ;; setup sorts
	   (let ((fopl-sentence-sort
		  (find-sort-in fopl-sentence-module sentence-sort))
		 (var-decl-list-sort
		  (find-sort-in fopl-sentence-module vardecl-sort)))
	     (if fopl-sentence-sort
		 (setq *fopl-sentence-sort* fopl-sentence-sort)
	       (with-output-panic-message ()
		 (princ "could not find sort FoplSentence")))
	     (if var-decl-list-sort
		 (setq *var-decl-list-sort* var-decl-list-sort)
	       (with-output-panic-message ()
		 (princ "could not find sort VarDeclList")))
	     )
	   ;; set up operators
	   (let ((var-decl-list (find-method-in fopl-sentence-module
						var-decl-list
						(list *cosmos*
						      *cosmos*)
						*var-decl-list-sort*))
		 (fopl-forall (find-method-in fopl-sentence-module
					      forall
					      (list *cosmos*
						    *fopl-sentence-sort*)
					      *fopl-sentence-sort*))
		 (fopl-exists (find-method-in fopl-sentence-module
					      exists
					      (list *cosmos*
						    *fopl-sentence-sort*)
					      *fopl-sentence-sort*))
		 (fopl-and (find-method-in fopl-sentence-module
					   and
					   (list *fopl-sentence-sort*
						 *fopl-sentence-sort*)
					   *fopl-sentence-sort*))
		 (fopl-or (find-method-in fopl-sentence-module
					  or
					  (list *fopl-sentence-sort*
						*fopl-sentence-sort*)
					  *fopl-sentence-sort*))
		 (fopl-imply (find-method-in fopl-sentence-module
					     imply
					     (list *fopl-sentence-sort*
						   *fopl-sentence-sort*)
					     *fopl-sentence-sort*))
		 (fopl-iff (find-method-in fopl-sentence-module
					   iff
					   (list *fopl-sentence-sort*
						 *fopl-sentence-sort*)
					   *fopl-sentence-sort*))
		 (fopl-neg (find-method-in fopl-sentence-module
					   not
					   (list *fopl-sentence-sort*)
					   *fopl-sentence-sort*))
		 (fopl-eq (if eq
			      (find-method-in fopl-sentence-module
					      eq
					      (list *cosmos*
						    *cosmos*)
					      *fopl-sentence-sort*)
			    :none))
		 (fopl-beq (if beq
			       (find-method-in fopl-sentence-module
					       beq
					       (list *cosmos*
						     *cosmos*)
					       *fopl-sentence-sort*)
			     :none))
		 )
	     ;;
	     (if (eq fopl-beq :none)
		 (setq *fopl-two-equalities* nil)
	       (setq *fopl-two-equalities* t))
	     ;;
	     (if (and var-decl-list fopl-forall fopl-exists fopl-and fopl-or
		      fopl-imply fopl-iff fopl-neg fopl-eq fopl-beq)
		 (setq *var-decl-list* var-decl-list
		       *fopl-forall* fopl-forall
		       *fopl-exists* fopl-exists
		       *fopl-and* fopl-and
		       *fopl-or* fopl-or
		       *fopl-imply* fopl-imply
		       *fopl-iff* fopl-iff
		       *fopl-neg* fopl-neg
		       *fopl-eq* (if (not (eq fopl-eq :none))
				     fopl-eq
				   nil)
		       *fopl-beq* (if (not (eq fopl-beq :none))
				      fopl-beq
				    nil))
	       (with-output-panic-message ()
		 (princ "could not install some operators in FoplSentence"))))
	   )
	  (t (with-output-panic-message ()
	       (princ "could not find FoplSentece module")))
	  )))

(defun install-fopl-clause ()
  (let ((fopl-clause-module (eval-modexp "FOPL-CLAUSE")))
    (let ((answer-method (find-method-in fopl-clause-module
					 '("$Ans")
					 (list *cosmos*)
					 *bool-sort*)))
      (unless answer-method
	(with-output-panic-message ()
	  (princ "could not install $Ans.")))
      (setq *fopl-ans* answer-method))))

;;; NOT USED
(defun install-fopl-clause-form ()
  (let ((fopl-clause-form-module (eval-modexp "FOPL-CLAUSE-FORM")))
    (cond ((and fopl-clause-form-module
		(not (modexp-is-error fopl-clause-form-module)))
	   (setq *fopl-clause-form-module* fopl-clause-form-module)
	   ;; setup sorts
	   (let ((fopl-clause-sort (find-sort-in fopl-clause-form-module
						"FoplClause"))
		 (fopl-sentence-seq-sort (find-sort-in fopl-clause-form-module
						     "FoplSentenceSeq")))
	     (if (and fopl-clause-sort fopl-sentence-seq-sort)
		 (setq *fopl-clause-sort* fopl-clause-sort
		       *fopl-sentence-seq-sort* fopl-sentence-seq-sort)
	       (with-output-panic-message ()
		 (princ "could not install some sorts of FOPL-CLAUSE-FORM"))))
	   ;; setup operators
	   (let ((clause-constructor (find-method-in fopl-clause-form-module
						     '("[" "_" "]")
						     (list *fopl-sentence-seq-sort*)
						     *fopl-clause-sort*))
		 (clause-constructor2 (find-method-in
				       fopl-clause-form-module
				       '("!" "[" "_" "]")
				       (list *fopl-sentence-seq-sort*)
				       *fopl-clause-sort*))
		 (fopl-sentence-seq (find-method-in
				    fopl-clause-form-module
				    '("_" ";" "_")
				    (list *fopl-sentence-seq-sort*
					  *fopl-sentence-seq-sort*)
				    *fopl-sentence-seq-sort*))
		 )
	     (if (and clause-constructor clause-constructor2
		      fopl-sentence-seq)
		 (setq *clause-constructor* clause-constructor
		       *clause-constructor2* clause-constructor2
		       *fopl-sentence-seq* fopl-sentence-seq)
	       (with-output-panic-message ()
		 (princ "could not install some operators in FOPL-CLAUSE-FORM")))
	     ))
	  (t (with-output-panic-message ()
	       (princ "could not find FOPL-CLAUSE-FORM")))
	  )))

;;; ***************
;;; PRIMITIVE UTILS
;;; ***************

#|
(defun fopl-sentence-type (sentence)
  (cond ((term-is-variable? sentence)
	 :atom)
	((term-is-application-form? sentence)
	 (let ((head (term-head sentence)))
	   (cond ((method-is-of-same-operator head *fopl-forall*)
		  :forall)
		 ((method-is-of-same-operator head *fopl-exists*)
		  :exists)
		 ((method-is-of-same-operator head *fopl-and*)
		  :and)
		 ((method-is-of-same-operator head *fopl-or*)
		  :or)
		 ((method-is-of-same-operator head *fopl-imply*)
		  :imply)
		 ((method-is-of-same-operator head *fopl-iff*)
		  :iff)
		 ((method-is-of-same-operator head *fopl-neg*)
		  :not)
		 ((method-is-of-same-operator head *fopl-eq*)
		  :eq)
		 ((method-is-of-same-operator head *fopl-beq*)
		  :beq)
		 (t :atom))))
	(t (with-output-panic-message ()
	     (princ "sentence-type accepted a illegual sentence")
	     (print-chaos-object sentence)))
	))
|#

#||
(defun fopl-sentence-type (sentence)
  (declare (type term sentence)
	   (values symbol))
  (cond ((term-is-variable? sentence) :atom)
	((term-is-builtin-constant? sentence) :atom)
	((term-is-lisp-form? sentence) :atom)
	((term-is-application-form? sentence)
	 (let ((head (term-head sentence)))
	   (cond ((eq head *fopl-forall*) :forall)
		 ((eq head *fopl-exists*) :exists)
		 ((eq head *fopl-and*)    :and)
		 ((eq head *fopl-or*)     :or)
		 ((eq head *fopl-imply*)  :imply)
		 ((eq head *fopl-iff*)     :iff)
		 ((eq head *fopl-neg*)     :not)
		 ((eq head *fopl-eq*)      :eq)
		 ((eq head *fopl-beq*)     :beq)
		 (t :atom))))
	(t (with-output-panic-message ()
	     (princ "sentence-type accepted a illegual sentence")
	     (print-chaos-object sentence)))
	))
||#

(defun fopl-sentence-type (sentence)
  (declare (type term sentence)
	   (values symbol))
  (cond ((term-is-application-form? sentence)
	 (let ((head (term-head sentence)))
	   (cond ((eq head *fopl-forall*) :forall)
		 ((eq head *fopl-exists*) :exists)
		 ((eq head *fopl-and*)    :and)
		 ((eq head *fopl-or*)     :or)
		 ((eq head *fopl-imply*)  :imply)
		 ((eq head *fopl-iff*)    :iff)
		 ((eq head *fopl-neg*)    :not)
		 ((eq head *fopl-eq*)     :eq)
		 ((eq head *fopl-beq*)    :beq)
		 (t :atom))))
	(t :atom)
	))

(declaim (inline fopl-forall?
		 fopl-exists?
		 fopl-and?
		 fopl-or?
		 fopl-imply?
		 fopl-iff?
		 fopl-not?
		 fopl-eq?
		 fopl-beq?
		 ))
(defun fopl-forall? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-forall*)))
(defun fopl-exists? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-exists*)))
(defun fopl-and? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-and*)))
(defun fopl-or? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-or*)))
(defun fopl-imply? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-imply*)))
(defun fopl-iff? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-iff*)))
(defun fopl-not? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-neg*)))
(defun fopl-eq? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-eq*)))
(defun fopl-beq? (f)
  (declare (type term f))
  (and (term-is-application-form? f)
       (eq (term-head f) *fopl-beq*)))
  
;;; IS-VALID-FORMULA? : Tterm -> Bool
;;;
(defun is-valid-formula? (term mod)
  (declare (type term term)
	   (type (or null module) mod))
  (unless mod
    (with-output-chaos-error ('internal)
      (princ "is-valid-formua?: called with no context module given, this should not happen.")))
  (is-in-same-connected-component (term-sort term)
				  *fopl-sentence-sort*
				  (module-sort-order mod)))

;;;
;;; CHECK-FOPL-SYNTAX
;;;
(defun check-fopl-syntax (fopl-sentence &optional report-error)
  (declare (type term fopl-sentence))
  (if (and (term? fopl-sentence)
	   (is-valid-formula? fopl-sentence *current-module*))
      (check-fopl-syntax-aux fopl-sentence report-error)
    (if report-error
	(with-output-chaos-error ('invalid-sentence)
	  (princ "encoutered with illegal sentence: ")
	  (print-next)
	  (print-chaos-object fopl-sentence))
      nil)))

(defun check-fopl-syntax-aux (fopl-sentence report-error)
  (labels ((check-var-decl (var-decl)
	     (cond ((term-is-variable? var-decl)
		    t)
		   ((and (term-is-application-form? var-decl)
			 (term-subterms var-decl))
		    (let ((top (term-head var-decl)))
		      (or (and (method-is-of-same-operator top
							   *var-decl-list*)
			       (every #'(lambda (x) (check-var-decl x))
				      (term-subterms var-decl)))
			  (if report-error
			      (with-output-chaos-error ('invalid-formula)
				(princ "invaid formula: ")
				(print-chaos-object fopl-sentence))
			    nil))))
		   (t (if report-error
			  (with-output-chaos-error ('invalid-formula)
			    (princ "encounterd with illegal formula")
			    (print-chaos-object fopl-sentence))
			nil)))))
    ;;
    (if (term-is-application-form? fopl-sentence)
	(let ((type (fopl-sentence-type fopl-sentence)))
	  (case type
	    (:atom t)
	    ((:forall :exists)
	     (and (check-var-decl (term-arg-1 fopl-sentence))
		  (check-fopl-syntax-aux (term-arg-2 fopl-sentence)
					 report-error)))
	    (:not
	     (check-fopl-syntax-aux (term-arg-1 fopl-sentence)
				    report-error))
	    (otherwise
	     (and (check-fopl-syntax-aux (term-arg-1 fopl-sentence)
					 report-error)
		  (check-fopl-syntax-aux (term-arg-2 fopl-sentence)
					 report-error)))))
      t)
    ))

;;; EOF
