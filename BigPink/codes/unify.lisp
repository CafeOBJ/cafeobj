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
			   File:unify.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; =======
;;; UNIFIER
;;; =======

(defun compose-subst (s1 s2)
  (declare (type list s1 s2))
  (labels ((add-new (s newsl)
	     (declare (type list s newsl))
	     (cond ((null s) newsl)
		   ((variable-image newsl (caar s))
		    (add-new (cdr s) newsl))
		   (t (cons (car s) (add-new (cdr s) newsl)))))
	   (composel (s1 s2)
	     (declare (type list s1 s2))
	     (cond ((null s1) nil)
		   (t (cons (cons (caar s1)
				  (apply-subst s2 (cdar s1)))
			    (composel (cdr s1) s2))))))
    ;;
    (if (car s2)
	(add-new s2 (composel s1 s2))
      s1)))

#||
(defun pn-decompose-terms-unify (t1 t2 ans)
  (macrolet ((add-bind-to-sub (v1 t1 sub)
	       `(let* ((pair (cons ,v1 ,t1))
		       (new-sub (normal-form-sub (list pair) ,sub)))
		  (unless new-sub
		    (return-from pn-decompose-terms-unify :fail))
		  new-sub)))
    (cond ((term-is-variable? t1)
	   (when (variable-eq t1 t2)
	     (return-from pn-decompose-terms-unify ans))
	   (when (occurs-in t1 t2)
	     (return-from pn-decompose-terms-unify :fail))
	   (let ((cval (variable-image ans t1)))
	     (if cval
		 (pn-decompose-terms-unify cval t2 ans)
	       (let ((s1 (term-sort t1))
		     (s2 (term-sort t2)))
		 (if (sort<= s2 s1 *current-sort-order*)
		     (add-bind-to-sub t1 t2 ans)
		   (if (term-is-variable? t2)
		       (if (sort<= s1 s2 *current-sort-order*)
			   (add-bind-to-sub t2 t1 ans)
			 :fail)
		     :fail)))))
	   )
	  ;;
	  ((term-is-variable? t2)
	   (pn-decompose-terms-unify t2 t1 ans))
	  ;;
	  ((term-is-builtin-constant? t1)
	   (if (term-builtin-equal t1 t2)
	       ans
	     :fail))
	  ((term-is-builtin-constant? t2)
	   :fail)
	  ;;
	  ((term-is-application-form? t1)
	   (let ((t1-top (term-head t1))
		 (t2-top (term-head t2)))
	     (if (method-is-of-same-operator t1-top t2-top)
		 (let ((t1-subterms (term-subterms t1))
		       (t2-subterms (term-subterms t2)))
		   (loop
		     (unless t1-subterms (return))
		     (setq ans (pn-decompose-terms-unify (car t1-subterms)
							 (car t2-subterms)
							 ans))
		     (when (eq ans :fail) (return))
		     (setq t1-subterms (cdr t1-subterms))
		     (setq t2-subterms (cdr t2-subterms)))
		   ans)
	       :fail)))
	  ;;
	  (t				;(term-is-builtin-constant? t2)
	   :fail
	   ))))
||#

(declaim (special .do-occur-check.))
(defvar .do-occur-check. t)

(defun pn-decompose-terms-unify (t1 t2 ans)
  (declare (type term t1 t2)
	   (type (or symbol list) ans)
	   ;; (values (or (member :fail) list))
	   (values (or symbol list)))
  (macrolet ((add-binding (v1 t1 sub)
	       `(cons (cons ,v1 ,t1) ,sub)))
    ;;
    (labels ((occurs-check (var x bindings)
	       (declare (type term var x)
			(list bindings))
	       (cond ((term-is-variable? x)
		      (or (term-eq var x)
			  (let ((cval (variable-image bindings x)))
			    (declare (type (or null term) cval))
			    (and cval
				 (occurs-check var cval bindings)))))
		     ((term-is-application-form? x)
		      (dolist (sub (term-subterms x))
			(when (occurs-check var sub bindings)
			  (return-from occurs-check t)))
		      nil)
		     (t nil)))
	     (var-unify (var x bindings)
	       (declare (type term var x)
			(type list bindings))
	       (let ((cval (variable-image bindings var))
		     ;; (x-is-var nil)
		     )
		 (declare (type (or null term) cval))
		 (when cval
		   (return-from var-unify
		     (pn-decompose-terms-unify cval x bindings)))
		 (when (term-is-variable? x)
		   ;; (setq x-is-var t)
		   (let ((cval2 (variable-image bindings x)))
		     (declare (type (or null term) cval2))
		     (when cval2
		       (return-from var-unify
			 (pn-decompose-terms-unify var cval2 bindings)))))
		 (when (and .do-occur-check.
			    (occurs-check var x bindings))
		   (return-from var-unify :fail))
		 ;;
		 (let ((s1 (term-sort var))
		       (s2 (term-sort x)))
		   (declare (type sort* s1 s2))
		   (if (sort<= s2 s1 *current-sort-order*)
		       (add-binding var x bindings)
		     #||
		     (if x-is-var
			 (if (sort<= s1 s2 *current-sort-order*) 
			     (add-binding x var bindings)
			   :fail)
		       :fail)
		     ||#
		     :fail ))))
	     )
      ;;
      (cond ((term-eq t1 t2)
	     (return-from pn-decompose-terms-unify ans))
	    ((term-is-variable? t1)
	     (var-unify t1 t2 ans))
	    ((term-is-variable? t2)
	     (var-unify t2 t1 ans))
	    ;;
	    ((term-is-builtin-constant? t1)
	     (if (term-builtin-equal t1 t2)
		 ans
	       :fail))
	    ((term-is-builtin-constant? t2)
	     :fail)
	    ;;
	    ((term-is-application-form? t1)
	     (let ((t1-top (term-head t1))
		   (t2-top (term-head t2)))
	       (declare (type method t1-top t2-top))
	       (if (method-is-of-same-operator t1-top t2-top)
		   (let ((t1-subterms (term-subterms t1))
			 (t2-subterms (term-subterms t2)))
		     (loop
		       (unless t1-subterms (return))
		       (setq ans (pn-decompose-terms-unify (car t1-subterms)
							   (car t2-subterms)
							   ans))
		       (when (eq ans :fail) (return))
		       (setq t1-subterms (cdr t1-subterms))
		       (setq t2-subterms (cdr t2-subterms)))
		     ans)
		 :fail)))
	    ;;
	    (t				;(term-is-builtin-constant? t2)
	     :fail
	     )))))

(defun pn-decompose-terms-match (t1 t2 ans)
  (declare (type term t1 t2)
	   (type (or (member :fail) list) ans)
	   (values (or (member :fail) list)))
  (macrolet ((add-bind-to-sub (v1 t1 sub)
	       `(cons (cons ,v1 ,t1) ,sub)))
    (cond ((term-is-variable? t1)
	   (let ((cval (variable-image ans t1)))
	     (declare (type (or null term) cval))
	     (if cval
		 (if (term-is-identical cval t2)
		     ans
		   :fail)
	       (if (sort<= (term-sort t2) (term-sort t1)
			   *current-sort-order*)
		   (add-bind-to-sub t1 t2 ans)
		 :fail)
	       )))
	  ;;
	  ((term-is-variable? t2) :fail)
	  ;;
	  ((term-is-builtin-constant? t1)
	   (if (term-builtin-equal t1 t2)
	       ans
	     :fail))
	  ((term-is-builtin-constant? t2) :fail)
	  ;;
	  ((term-is-application-form? t1)
	   (let ((t1-top (term-head t1))
		 (t2-top (term-head t2)))
	     (declare (type method t1-top t2-top))
	     (if (method-is-of-same-operator t1-top t2-top)
		 (let ((t1-subterms (term-subterms t1))
		       (t2-subterms (term-subterms t2)))
		   (loop
		     (unless t1-subterms (return))
		     (setq ans (pn-decompose-terms-match (car t1-subterms)
							 (car t2-subterms)
							 ans))
		     (when (eq ans :fail) (return))
		     (setq t1-subterms (cdr t1-subterms))
		     (setq t2-subterms (cdr t2-subterms)))
		   ans)
	       :fail)))
	  ;;
	  (t				;(term-is-builtin-constant? t2)
	   :fail
	   ))))

;;; UNIFY : TERM1 TERM2 SUBST -> {SUBST, NO-MATCH, E-MATCH}
;;;
(defun unify (t1 t2 &optional subst)
  (declare (type term t1 t2)
	   (list subst))
  (if (pn-flag unify-heavy)
      (let ((*do-unify* t))
	(multiple-value-bind (gst new-subst no-match e-eq)
	    (first-match t1 t2 subst)
	  (declare (ignore gst)
		   (type list new-subst))
	  (when no-match
	    (return-from unify (values nil t nil)))
	  (when e-eq
	    (return-from unify (values subst nil t)))
	  (setq subst
	    (compose-subst subst new-subst))
	  (values subst nil nil))
	)
    ;; simple nonE-theory unification.
    (let ((ans (pn-decompose-terms-unify t1 t2 subst)))
      #||
      (when *match-debug*
	(with-output-simple-msg ()
	  (princ "*** UNIFY")
	  (print-next)
	  (princ "t1 = ")(term-print t1)
	  (print-next)
	  (princ "t2 = ")(term-print t2))
	)
      ||#
      (if (eq ans :fail)
	  (values nil t nil)
	(if ans
	    (let ((sub (normal-form-sub ans nil))
		  ;; (sub ans)
		  )
	      #||
	      (when *match-debug*
		(with-output-simple-msg ()
		  (princ "- UNIFY: subst = ")
		  (print-substitution sub)))
	      ||#
	      (values sub nil nil)
	      )
	  (progn
	    #||
	    (when *match-debug*
	      (with-output-simple-msg ()
		(princ "- UNIFY: e-equal")))
	    ||#
	    (values subst nil t))))
      )))

(declaim (inline prop-unify))

(defun prop-unify (gpat t2)
  (declare (type term gpat t2))
  (if (term-is-identical gpat t2)
      (values nil nil t)
    (values nil t nil)))

(defun first-unify (t1 t2 &optional subst)
  (declare (type term t1 t2)
	   (type list subst))
  (let ((*do-unify* t))
    (multiple-value-bind (gst new-subst no-match e-eq)
	(first-match t1 t2 subst)
      (when no-match
	(return-from first-unify (values nil nil t nil)))
      (when e-eq
	(return-from first-unify (values gst subst nil t)))
      (setq subst
	(compose-subst subst new-subst))
      (values gst subst nil nil))
    ))

(defun next-unify (gst)
  (let ((*do-unify* t))
    (next-match gst)))

;;; =======
;;; MATCHER
;;; =======
(defun pn-match (t1 t2 &optional subst one-way-match)
  (declare (type term t1 t2)
	   (type list subst))
  #||
  (when *match-debug*
    (with-output-msg ()
      (princ "pn-match:")
      (print-next)
      (princ "t1 = ") (term-print t1)
      (print-next)
      (princ "t2 = ") (term-print t2)
      (when subst
	(print-next)
	(princ "subst = ") (print-substitution subst))))
  ||#
  (if (pn-flag unify-heavy)
      (let ((*do-unify* nil)
	    (*one-way-match* one-way-match))
	(multiple-value-bind (gst new-subst no-match e-eq)
	    (first-match t1 t2 subst)
	  (declare (ignore gst)
		   (type list new-subst))
	  (when no-match
	    (return-from pn-match (values nil t nil)))
	  (when e-eq
	    (return-from pn-match (values subst nil t)))
	  (setq subst
	    (compose-subst subst new-subst))
	  (return-from pn-match (values subst nil nil))))
    ;; simple nonE-theory match
    (let* ((*one-way-match* one-way-match)
	   (ans (pn-decompose-terms-match t1 t2 subst)))
      (if (eq ans :fail)
	  (values nil t nil)
	(if ans
	    (values ans nil nil)
	  (values subst nil t))
	))))

#||
(defun pn-match-2 (t1 t2 &optional subst)
  (let ((*do-unify* nil)
	(*one-way-match* t))
    (multiple-value-bind (gst new-subst no-match e-eq)
	(first-match t1 t2 subst)
      (declare (ignore gst))
      (when no-match
	(return-from pn-match-2 (values nil t nil)))
      (when e-eq
	(return-from pn-match-2 (values subst nil t)))
      (setq subst
	(compose-subst subst new-subst))
      (return-from pn-match-2 (values subst nil nil)))
    ))
||#

;;; EOF

  
