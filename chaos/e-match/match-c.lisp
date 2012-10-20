;;;-*- Mode:Lisp; Syntax:CommonLisp; Package: CHAOS -*-
;;; $Id: match-c.lisp,v 1.2 2010-05-30 04:34:42 sawada Exp $
(in-package :chaos)
#|==============================================================================
				  System:Chaos
				 Module:e-match
			       File:match-c.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDURES for C Matching ==================================================
;;; BASED ON matcher of OBJ3 Interpreter of SRI International:
;;; Copyright 1988,1991 SRI International.  All right reserved.

;;; COMMUTATIVE STATE 
;;;
;;; The commutative state consists into an array of booleen and the original 
;;; system. The state of booleen represent the state of the exploration of 
;;; all the permutation. It has to be see as the representation in basis 
;;; 2 of a number < 2^r.
;;;

(defstruct (match-C-state
	    ; (:type vector)
	    (:constructor create-match-C-state (count sys)))
  (count 0 :type fixnum)
  (sys nil :type list))

;;; INTIALIZATION

;;; Initialize a commutative state. It check if the top symbols of each equation
;;; of the system have the same (commutative) head function.

(defun match-C-state-initialize (sys env)
  (declare (ignore env)
	   (type list sys))
  (block no-match
    (dolist (equation (m-system-to-list sys))
      (unless (and (not (term-is-variable? (equation-t2 equation)))
		   (method-is-commutative-restriction-of
		    (term-method (equation-t2 equation))
		    (term-method (equation-t1 equation))))
	(return-from no-match (values nil t))))
    (values (create-match-C-state 0 sys)
	    nil)))

;;; NEXT STATE

(defun match-C-next-state (C-st)
  (declare (type match-c-state))
  (let* ((N   (match-C-state-count C-st))
	 (sys (match-C-state-sys C-st))
	 (q   N)
	 (r   0)
	 (point (m-system-to-list sys))
	 (equation nil)
	 (t1 nil)
	 (t2 nil)
	 (new-sys (new-m-system))
	 (lg (length point))
	 )
    (declare (type fixnum q r lg N)
	     (type list point))
    (if (= N (the fixnum (expt2 (the fixnum lg))))
	;; there is no more match-C-state
	(values nil nil t)
	(progn 
	  (dotimes-fixnum (k lg)
	    #+KCL (setq r (rem q 2) q (truncate q 2))
	    #-KCL (multiple-value-setq (q r) (truncate q 2))
	    (setq equation (car point)
		  point (cdr point)
		  t1 (equation-t1 equation)
		  t2 (equation-t2 equation))
	    (cond ((= r 0) 
		   (add-equation-to-m-system new-sys 
					     (make-equation (term-arg-1 t1) 
							    (term-arg-1 t2)))
		   (add-equation-to-m-system new-sys 
					     (make-equation (term-arg-2 t1) 
							    (term-arg-2 t2))))
		  (t (add-equation-to-m-system new-sys 
					       (make-equation (term-arg-1 t1) 
							      (term-arg-2 t2)))
		     (add-equation-to-m-system new-sys 
					       (make-equation (term-arg-2 t1) 
							      (term-arg-1 t2))))))
	  (setf (match-C-state-count C-st) (1+ N))
	  (values new-sys C-st nil)
	  ))))


;;; EQUALITY

;;; "t1" and "t2" are supposed to be terms with same head commutative symbol
;;;
(defun match-C-equal (t1 t2)
  (declare (type term t1 t2))
  (if (term-is-applform? t2)
      (if (method-is-of-same-operator (term-head t1) (term-head t2))
	  (if (term-equational-equal (term-arg-1 t1) (term-arg-1 t2))
	      (term-equational-equal (term-arg-2 t1) (term-arg-2 t2))
	      (if (term-equational-equal (term-arg-1 t1) (term-arg-2 t2))
		  (term-equational-equal (term-arg-2 t1) (term-arg-1 t2))
		  nil))
	  nil)
      nil))
	      

;;; EOF
