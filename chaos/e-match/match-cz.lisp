;;;-*- Mode:Lisp; Syntax:CommonLisp; Package: CHAOS -*-
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
			       File:match-cz.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDUREs for CZ Matching =================================================

;;;  CZ: commutativity with identity
;;;


;; The idea is that there are only two possible matches for any 
;; pair of commutative terms - 11 and 22, or 12 and 21.  Since we
;; may actually get a system of multiple equations, we have to 
;; generate all possible pairings.
;;
;; Also, we check for identity binding possibilities for each of the 
;; four immediate subterms.  Thus there are 4 possible match sub-equations
;; where one term is dropped, and 4 possible match sub-equations where
;; two terms are dropped.
;;
;; current understanding is that the cases with two terms dropped
;; due to identity are not needed, since e.g. 4 = 4*1   must be 
;; handled by the matching algorithm anyway.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defstruct (match-CZ-state
	     (:constructor create-match-cz-state (n sys)))
  (n 0 :type fixnum)
  (sys nil :type list))

;;; CZ STATE INITIALIZATION

;;; t1 of each eq of sys is pattern, has variables.  t2 is (ground) term.

(defun match-CZ-state-initialize (sys env)
  (declare (ignore env)
	   (type list sys))
  ;; env : why isn't env used here or in C$?
  (values (create-match-cz-state 0 sys) nil))

;;; NEXT CZ State

;;; if we have only one equation to solve, then this will simply
;;; count from 0 to 5, where each number determines a particular
;;; solution to the equation modulo CZ.  If we have more equations,
;;; then we have to generate all possibilities - (0-5)*(0-5)*...*(0-5)
;;; we keep track of which solution to try next with one integer which
;;; enumerates all possible solutions.

(defun match-CZ-next-state (CZ-st)
  (declare (type match-cz-state cz-st)
	   (values list (or null match-cz-state) (or null t)))
  (let* ((sys (match-cz-state-sys CZ-st))
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
	     (type list new-sys point))
    (do* ((N (match-cz-state-n CZ-st))
	  (q N N)
	  )
	 ((or (not (m-system-is-empty? new-sys))
	      (>= N (the fixnum (expt 6 (the fixnum lg)))))
	  (progn 
	    (setf (match-cz-state-n CZ-st) N)
	    (if (not (m-system-is-empty? new-sys))
		(values new-sys CZ-st nil) ;succes case
		(values nil nil t))))	; fail case
      (declare (type fixnum n q))
      (incf N)				; try the next N
      (dotimes-fixnum (k lg)		; k = lg,...,1
					; this treats q as a bitvector in base 6
	#+KCL (setq r (rem q 6) q (truncate q 6))
	#-KCL (multiple-value-setq (q r) (truncate q 6))
	(setq equation (car point)
	      point (cdr point)
	      t1 (equation-t1 equation)
	      t2 (equation-t2 equation)
	      meth1 (if (or (term-is-constant? t1)
			    (term-is-variable? t1))
			nil 
			(term-method t1))
	      meth2 (if (or (term-is-constant? t2)
			    (term-is-variable? t2))
			nil 
			(term-method t2)))
	(cond ((and (= r 0)		; as if no thoery applied - 11 22
		    meth1 meth2)
	       (add-equation-to-m-system new-sys 
					 (make-equation (term-arg-1 t1) 
							(term-arg-1 t2)))
	       (add-equation-to-m-system new-sys 
					 (make-equation (term-arg-2 t1) 
							(term-arg-2 t2))))
	      ((and (= r 1)		; comm - 12 21
		    meth1 meth2)	;
	       (add-equation-to-m-system new-sys 
					 (make-equation (term-arg-1 t1) 
							(term-arg-2 t2)))
	       (add-equation-to-m-system new-sys 
					 (make-equation (term-arg-2 t1) 
							(term-arg-1 t2))))
	      ((and (= r 2)
		    meth1		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-1 t1) meth1)))
	       (add-equation-to-m-system new-sys
					 (make-equation (term-arg-1 t1)
							(term-make-zero meth1)))
	       (add-equation-to-m-system new-sys
					 (make-equation (term-arg-2 t1) t2)))
	      ((and (= r 3)
		    meth1		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-2 t1) meth1)))
	       (add-equation-to-m-system new-sys
					 (make-equation (term-arg-2 t1)
							(term-make-zero meth1)))
	       (add-equation-to-m-system new-sys
					 (make-equation (term-arg-1 t1) t2)))
	      ;; note these are redundant if we have terms 
	      ;; in normal form (no identities).
	      ((and (= r 4)
		    meth2		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-1 t2) meth2)))
	       (let ((zero (term-make-zero meth2)))
		 (when zero
		   (add-equation-to-m-system new-sys
					     (make-equation zero
							    (term-arg-1 t2))))
		 (add-equation-to-m-system new-sys
					   (make-equation t1 (term-arg-2 t2)))))
	      ((and (= r 5)
		    meth2		; term is non atomic
		    (not (term-is-zero-for-method (term-arg-2 t2) meth2)))
	       (let ((zero (term-make-zero meth2)))
		 (when zero
		   (add-equation-to-m-system new-sys
					     (make-equation zero
							    (term-arg-2 t2))))
		 (add-equation-to-m-system new-sys
					   (make-equation t1 (term-arg-1 t2)))))
	      (t nil))))))


;;; CZ Equality

;;; same comment as above applies here - 
;;; we don't return the other possible solutions because they
;;; are subsumed by the ones present here.
;;; match-CZ-equal assumes non-atomic args.

(defun match-CZ-equal (t1 t2)
  (declare (type term t1 t2)
	   (values (or null t)))
  (let ((meth1 (term-head t1))
	(meth2 (term-head t2)))
  (or (term-is-similar? t1 t2)		; was equal
      (and (term-is-zero-for-method (term-arg-1 t1) meth1)
	   (term-equational-equal (term-arg-2 t1) t2))
      (and (term-is-zero-for-method (term-arg-2 t1) meth1)
	   (term-equational-equal (term-arg-1 t1) t2))
      (and (term-is-zero-for-method (term-arg-1 t2) meth2)
	   (term-equational-equal t1 (term-arg-2 t2)))
      (and (term-is-zero-for-method (term-arg-2 t2) meth2)
	   (term-equational-equal t1 (term-arg-1 t2)))
      (and (term-equational-equal (term-arg-1 t1) (term-arg-1 t2))
	   (term-equational-equal (term-arg-2 t1) (term-arg-2 t2)))
      (and (term-equational-equal (term-arg-1 t1) (term-arg-2 t2))
	   (term-equational-equal (term-arg-2 t1) (term-arg-1 t2))))))

;;; EOF
