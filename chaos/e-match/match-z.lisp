;;;-*- Mode:Lisp; Syntax:CommonLisp; Package:CHAOS -*-
;;; $Id: match-z.lisp,v 1.2 2007-04-03 06:46:14 sawada Exp $
(in-package :chaos)
#|==============================================================================
				  System:Chaos
				 Module:e-match
			       File:match-z.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDURES for Identity Matching ===========================================
;;; BASED ON matcher of OBJ3 Interpreter of SRI International:
;;; Copyright 1988,1991 SRI International.  All right reserved.

;;; Zero (Identity) STATE
;;;

(defstruct (match-z-state
	     (:constructor create-match-z-state (n sys)))
  (n 0 :type fixnum)
  (sys nil :type list)			; match system
  )

;;; INITIALIZATION

;;; t1 of each eq of sys is pattern, has variables.  t2 is (ground) term-

(defun match-Z-state-initialize (sys env)
  (declare (ignore env))
  ;; env why isn't env used here or in match-C?
  (values (create-match-z-state 0 sys) nil))

;;; NEXT STATE

(defun match-Z-next-state (Z-st)
  (let* ((sys (match-z-state-sys Z-st))
	 (point (m-system-to-list sys))
	 (equation nil)
	 (r 0)
	 (t1 nil)
	 (t2 nil)
	 (new-sys (new-m-system))
	 (lg (length point))
	 (meth1 nil)
	 (meth2 nil)
	 )
    (declare (type fixnum r lg)
	     (type list point new-sys))
    (do* ((N (match-z-state-n Z-st))
	  (q N N)
	  (point2 point point))
	 ((or (not (m-system-is-empty? new-sys))
	      (>= N (the fixnum (expt 5 (the fixnum lg)))))
	  (progn (setf (match-z-state-n Z-st) N)
		 (if (not (m-system-is-empty? new-sys))
		     (values new-sys Z-st nil) ;success case
		     (values nil nil t)))) ; fail case
      (declare (type fixnum n q))
      (incf N)				; try the next N
      (dotimes (k lg)			; k = lg,...,1
	(declare (type fixnum k))	; this treats q as a bitvector in base 5
	(multiple-value-setq (q r) (truncate q 5))
	(setq equation (car point2)
	      point2 (cdr point2)
	      t1 (equation-t1 equation)
	      t2 (equation-t2 equation)
	      meth1 (if (term-is-constant? t1) ; note veriable also returns t
			nil 
			(term-method t1))
	      meth2 (if (term-is-constant? t2)
			nil 
			(term-method t2)))
	;;
	(when *match-debug*
	  (format t "~%z-next-state: k = ~d, r = ~d" k r)
	  (format t "~% term1 = ")
	  (print-chaos-object t1)
	  (format t "~% meth1 = ")
	  (print-chaos-object meth1)
	  (format t "~% term2 = ")
	  (print-chaos-object t2)
	  (format t "~% meth2 = ")
	  (print-chaos-object meth2))
	;;
	(cond ((and (= r 0)		; as if no thoery applied - 11 22
		    meth1 meth2
		    (method-is-of-same-operator+ meth1 meth2))
	       (add-equation-to-m-system new-sys 
					 (make-equation (term-arg-1 t1) 
							(term-arg-1 t2)))
	       (add-equation-to-m-system new-sys 
					 (make-equation (term-arg-2 t1) 
							(term-arg-2 t2))))
	      ((and (= r 1)
		    meth1		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-1 t1) meth1)))
	       (let ((zero (term-make-zero meth1)))
		 (when zero
		   (add-equation-to-m-system new-sys
					     (make-equation (term-arg-1 t1)
							    (term-make-zero meth1)))
		   (add-equation-to-m-system new-sys
					     (make-equation (term-arg-2 t1) t2)))))
	      ((and (= r 2)
		    meth1		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-2 t1) meth1)))
	       (let ((zero (term-make-zero meth1)))
		 (when zero
		   (add-equation-to-m-system new-sys
					     (make-equation (term-arg-2 t1)
							    zero))
		   (add-equation-to-m-system new-sys
					     (make-equation (term-arg-1 t1) t2)))))
	      ;; note these are redundant if we have terms 
	      ;; in normal form (no identities).
	      ((and (= r 3)
		    meth2		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-1 t2) meth2)))
	       (let ((zero (term-make-zero meth2)))
		 (when zero
		   (add-equation-to-m-system new-sys
					     (make-equation zero
							    (term-arg-1 t2)))
		   (add-equation-to-m-system new-sys
					     (make-equation t1 (term-arg-2 t2))))))
	      ((and (= r 4)
		    meth2		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-2 t2) meth2)))
	       (let ((zero (term-make-zero meth2)))
		 (when zero
		   (add-equation-to-m-system new-sys
					     (make-equation zero
							    (term-arg-2 t2)))
		   (add-equation-to-m-system new-sys
					     (make-equation t1 (term-arg-1 t2))))))
	      (t nil))))))

;;; EQUALITY

;;; predicate which is true if t1 and t2 are equal modulo identity rule.
;;; match-Z-equal assumes non-atomic args.
;;;
(defun match-Z-equal (t1 t2)
  (declare (type term t1 t2)
	   (values (or null t)))
  (if (term-is-applform? t2)
      (let ((meth1 (term-head t1))
	    (meth2 (term-head t2)))
	(if (method-is-of-same-operator meth1 meth2)
	    (or
	     (and (term-is-zero-for-method (term-arg-1 t1) meth1)
		  (term-equational-equal (term-arg-2 t1) t2))
	     (and (term-is-zero-for-method (term-arg-2 t1) meth1)
		  (term-equational-equal (term-arg-1 t1) t2))
	     (and (term-is-zero-for-method (term-arg-1 t2) meth2)
		  (term-equational-equal t1 (term-arg-2 t2)))
	     (and (term-is-zero-for-method (term-arg-2 t2) meth2)
		  (term-equational-equal t1 (term-arg-1 t2)))
	     (and (term-equational-equal (term-arg-1 t1) (term-arg-1 t2))
		  (term-equational-equal (term-arg-2 t1) (term-arg-2 t2))))
	    nil))
      nil))

;;; EOF
