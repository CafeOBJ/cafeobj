;;;-*- Mode:LISP; Package:CAFEIN; Base:10; Syntax:Common-lisp -*-
;;; $Id: match-utils.lisp,v 1.2 2007-04-03 06:46:14 sawada Exp $
(in-package :chaos)
#|==============================================================================
				  System:Chaos
				 Module:e-match
			     File:match-utils.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; BASED ON matcher of OBJ3 Interpreter of SRI International:
;;; Copyright 1988,1991 SRI International.  All right reserved.

;;; POSSIBLY-MATCHES : PATTERN TARGET -> BOOL
;;;-----------------------------------------------------------------------------
;;; returns t iff the pattern and target may match.
;;; must be accurate when answer is false.

;;; possibly-matches-non-ver
;;; assume that t1,t2 are not a variables.
;;;
(defun possibly-matches-nonvar (t1 t2)
  (declare (type term t1 t2)
	   (values (or null t)))
  (cond ((term-is-builtin-constant? t1)
	 (term-builtin-equal t1 t2))
	((term-is-builtin-constant? t2) nil)
	(t 
	 (let* ((meth1 (term-head t1))
		(meth2 (term-head t2))
		(th-info-1 (method-theory-info-for-matching meth1))
		(th-info-2 (method-theory-info-for-matching meth2)))
	   (if (not (method-is-of-same-operator+ meth1 meth2))
	       ;; built-in identity matching requires a change here
	       ;; somehow the usage of theories seems messy here.
	       (if (test-theory .Z. (theory-info-code th-info-1))
		   ;; too costly?
		   (or (possibly-matches (term-arg-1 t1) t2)
		       (possibly-matches (term-arg-2 t1) t2))
		   nil)
	       (let ((chk1 (theory-info-empty-for-matching th-info-1))
		     (chk2 (theory-info-empty-for-matching th-info-2)))
		 (if (and chk1 chk2)
		     (let ((subs1 (term-subterms t1))
			   (subs2 (term-subterms t2))
			   (ok? t))
		       (while subs1
			 (unless (possibly-matches (car subs1) (car subs2))
			   (setq ok? nil)
			   (return))
			 (setq subs1 (cdr subs1)
			       subs2 (cdr subs2)))
		       ok?)
		     t)))))))

;; could improve on this
(defun possibly-matches (t1 t2)
  (declare (type term t1 t2)
	   (values (or null t)))
  (cond ((term-is-variable? t1) t)
	((term-is-variable? t2) nil)
	(t (possibly-matches-nonvar t1 t2))))

;;; EOF
