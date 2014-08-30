;;;-*- Mode: Lisp; Syntax: CommonLisp Package: CHAOS -*-
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
				 Module:e-match
			       File:match-e.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDURES for Syntactic Matching ==========================================

;;; NOTE:
;;; It would be certainly more efficient to built in the empty theory in
;;; the mutation process of a (non empty) theory.

;;; Implementation

;;; An empty state consists into a system and a flag 0 or 1. 
;;; 0 means that the state is a new one and that one as to decompose the system.
;;; 1 means that the decomposition has been already done and that there is 
;;; no more next state

#|
(defstruct (match-empty-state (:constructor create-match-empty-state (flag sys)))
  (flag 0 :type bit)
  sys )

(defmacro match-empty-state-flag (_s*) `(car ,_s*))
(defmacro match-empty-state-sys (s_*) `(cdr ,s_*))
(defmacro create-match-empty-state (_***flag _***sys) `(cons ,_***flag ,_***sys))

(defvar .match-empty-state. nil)
(eval-when (:execute :load-toplevel)
  (setq .match-empty-state. (create-match-empty-state 0 nil)))

(defun the-match-empty-state () .match-empty-state.)

|#

;;; INITIALIZATION

;;; Initialize an empty state. It check if the top symbols of each equation of
;;; the system have the same head function.
;;;
(defun match-empty-state-initialize (sys env)
  (declare (ignore env)
	   (type list sys)
	   (values (or null t) (or null t)))
  (block no-match
    (dolist (equation (m-system-to-list sys))
      (let ((lhs (equation-t1 equation))
	    (rhs (equation-t2 equation)))
	#||
	(when (or (term-is-builtin-constant? rhs)
		  (term-is-variable? rhs))
	  (return-from no-match (values nil t)))
	||#
	(unless (term-type-eq lhs rhs)
	  (return-from no-match (values nil t)))
	(unless (or (match-empty-equal lhs rhs)
		    (and (term-is-application-form? lhs)
			 (method-is-of-same-operator+ (term-head lhs)
						      (term-head rhs))))
	  (return-from no-match (values nil t))))
      )
    (values (create-match-empty-state 0 sys) nil)))


;;; NEXT STATE

(defun match-empty-next-state (empty-st)
  (declare (type list empty-st)
	   (values list list (or null t)))
  #||
  (unless empty-st
    (with-output-chaos-warning ()
      (format t "match empty next PANIC: illegal situation, the null state!"))
    (break)
    (return-from match-empty-next-state (values nil nil t)))
  ||#
  (let ((flag (match-empty-state-flag empty-st))
	(sys (match-empty-state-sys empty-st)))
    (declare (type fixnum flag)
	     (type list sys))
    (if (= flag 1)
	;; no more state
	(values nil nil t)
	(multiple-value-bind (new-m-sys no-match)
	    (match-decompose&merge (create-match-system (new-environment)
							sys))
	  (if no-match
	      (values nil nil t)
	      (progn
		(setf (match-empty-state-flag empty-st) 1)
		(values (match-system-to-m-system new-m-sys) 
			empty-st
			nil)))))))

;;; EQUALITY

;;; Assumption:
;;; - t1 and t2 are not variables.
;;;
(defun match-empty-equal (t1 t2)
  (declare (type term t1 t2)
	   (values (or null t)))
  (cond ((term-is-builtin-constant? t1)
	 (term-builtin-equal t1 t2))
	((term-is-builtin-constant? t2) nil)
	(t (let ((head1 (term-head t1))
		 (head2 (term-head t2))
		 (subs1 (term-subterms t1))
		 (subs2 (term-subterms t2)))
	     (if (null subs1)
		 (and (null subs2)
		      (eq head1 head2))
		 (if (method-is-of-same-operator head1 head2)
		     (do* ((sub1 subs1 (cdr sub1))
			   (sub2 subs2 (cdr sub2))
			   (st1 nil)
			   (st2 nil))
			  ((null sub1) t)
		       (setq st1 (car sub1))
		       (setq st2 (car sub2))
		       ;; (unless st2 (return nil))
		       (cond ((term-is-variable? st1)
			      (unless (variable= st1 st2) (return nil))
			      )
			     ((term-is-variable? st2) (return nil))
			     ((term-is-builtin-constant? st1)
			      (unless (term-builtin-equal st1 st2) (return nil)))
			     (t (unless (if (theory-info-empty-for-matching
					     (method-theory-info-for-matching
					      (term-method st1)))
					    (match-empty-equal st1 st2)
					    (term-equational-equal st1 st2))
				  (return nil)))))
		     nil))))))

;;; EOF
