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
			      File:match-acz.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (safety 3) #-GCL (debug 2)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDURES for ACZ Matching ================================================

;;;-----------------------------------------------------------------------------
;;; Originally written by Patrick Lincoln,
;;; SRI Declarative Languate Projects, CSL, SRI. for OBJ3 system.
;;; All the functions for ACZ matching in the OBJ3 system adopted to Chaos
;;; by T. Sawada, Software Enginnering Lab., SRA, Inc. <sawada@sra.co.jp>
;;;-----------------------------------------------------------------------------

#||
(defstruct match-ACZ-state
  methods				; array[meth] the top level mthods of
					; each eqn in the system.
  LHS-f					; array[term] functional terms.
  LHS-v					; array[term] variables.
  RHS-c					; array[term] constants.
  RHS-f					; array[term] functional terms.
  LHS-f-r				; array[bool]  notes repeated functional
					; terms.
  LHS-v-r				; array[bool] notes repeated variables.
  RHS-c-r				; array[bool] notes repeated constants.
  RHS-f-r				; array[bool] notes repeated functional
					; terms.
  (LHS-mask 0)				; long int variables and funs accounted
					; for by RHS-c-sol.
  (LHS-f-mask 0)			; long int funs accounted for by
					; RHS-c-sol. 
  (LHS-r-mask 0)			; long int bitvector of all repeated
					; (>0) terms on lhs.
  RHS-c-sol				; array[int] solution matrix constants.
  RHS-c-max				; int max value of elements of
					; RHS-c-sol. 
  RHS-f-sol				; array[int] solution matrix functional
					; terms.
  RHS-f-max				; int max value of elements of
					; RHS-f-sol. 
  RHS-full-bits				; int 11111...111.
  RHS-c-compat				; array[int] array of compatibility
					; bitvectors.
  RHS-f-compat				; array[int] array of compatibility
					; bitvectors.
  LHS-c-count				; int number of constants on LHS after
					; simplification.
  LHS-f-count				; int number of functions on LHS after
					; simplification.
  LHS-v-count				; int number of variables on LHS after
					; simplification.
  RHS-c-count				; int number of constants on RHS after
					; simplification.
  RHS-f-count				; int number of functions on RHS after
					; simplification.
  (no-more nil)				; when true implies that all solutions
					; have been reported.
  )
||#

(defvar *use-one-var-opt* nil)

;;; Uses array implementation instead of structure, just the same as MATCH-AC
;;;
(defmacro make-match-ACZ-state ()  `(alloc-svec 27))

;;; the toplevel operators of each equation in the system
;;; type : array[term]
(defmacro match-acz-state-methods (state__) `(svref ,state__ 0))

;;; functional terms
;;; type : array[term]
(defmacro match-acz-state-lhs-f (state__) `(svref ,state__ 1))

;;; variables on the LHS
;;; type : array[term]
(defmacro match-acz-state-lhs-v (state__) `(svref ,state__ 2))

;;; contants on the RHS
;;; type : array[term]
(defmacro match-acz-state-rhs-c (state__) `(svref ,state__ 3))

;;; functional terms on RHS
;;; type : array[term]
(defmacro match-acz-state-rhs-f (state__) `(svref ,state__ 4))

;;; notes repeated functional terms of LHS
;;; type : array[bool]
(defmacro match-acz-state-lhs-f-r (state__) `(svref ,state__ 5))

;;; notes repeated variables of LHS
;;; type : array[bool]
(defmacro match-acz-state-lhs-v-r (state__) `(svref ,state__ 6))

;;; notes repeated constants of RHS
;;; type : array[bool]
(defmacro match-acz-state-rhs-c-r (state__) `(svref ,state__ 7))

;;; notes repreated funcational terms of RHS
;;; type : array[bool]
(defmacro match-acz-state-rhs-f-r (state__) `(svref ,state__ 8))

;;; variables and funs acocunted for by RHS-c-sol
;;; type : fixnum
(defmacro match-acz-state-lhs-mask (state__)  `(svref ,state__ 9))

;;; funs accounted for by RHS-c-sol
;;; type : fixnum
(defmacro match-acz-state-lhs-f-mask (state__) `(svref ,state__ 10))

;;; bit vector of all repeated (> 0) terms on LHS
(defmacro match-acz-state-lhs-r-mask (state__)  `(svref ,state__ 11))

;;; solution matrix for constants
;;; type : array[fixnum]
(defmacro match-acz-state-rhs-c-sol (state__) `(svref ,state__ 12 ))

;;; max value of elements of RHS-C-sol
;;; type : fixnum
(defmacro match-acz-state-rhs-c-max (state__) `(svref ,state__ 13))

;;; solutions matrix; functional terms
;;; type : array[fixnum]
(defmacro match-acz-state-rhs-f-sol (state__) `(svref ,state__ 14))

;;; max value of elements of RHS-f-sol
;;; type : fixnum
(defmacro match-acz-state-rhs-f-max (state__) `(svref ,state__ 15))

;;; type : fixnum 11111 ... 1111
(defmacro match-acz-state-rhs-full-bits (state__) `(svref ,state__ 16))

;;; array of compatibility bitvectors; constants
;;; type : array[fixnum]
(defmacro match-acz-state-rhs-c-compat (state__) `(svref ,state__ 17))

;;; array of compatibility bitvectors; funcs
;;; type : array[fixnum]
(defmacro match-acz-state-rhs-f-compat (state__) `(svref ,state__ 18))

;;; number of constants on LHS after simplification
;;; type : fixnum
(defmacro match-acz-state-lhs-c-count (state__) `(svref ,state__ 19))

;;; number of functions on LHS after simplification
;;; type : fixnum
(defmacro match-acz-state-lhs-f-count (state__) `(svref ,state__ 20))

;;; number of variables on LHS after simplification
;;; type : fixnum
(defmacro match-acz-state-lhs-v-count (state__) `(svref ,state__ 21))

;;; number of constants on RHS after simplification
;;; type : fixnum
(defmacro match-acz-state-rhs-c-count (state__)  `(svref ,state__ 22))

;;; number of functions on RHS after simplification
;;; type : fixnum
(defmacro match-acz-state-rhs-f-count (state__) `(svref ,state__ 23))

;;; t iff all solutions have been reported.
(defmacro match-acz-state-no-more (state__) `(svref ,state__ 24))

;;; type tag: 
;;; type : symbol
(defmacro match-acz-state-acz-state-p (state__)  `(svref ,state__ 25))

(defmacro match-acz-state-zero-matches (state__) `(svref ,state__ 26))

(declaim (inline match-acz-state-p))
(#+GCL si::define-inline-function #-GCL defun match-acz-state-p (state)
  (and (vectorp state)
       (eq (svref state 25) 'acz-state)))

;;; the following is used only when we boil it down to a single var on left.
;;; it is only for performance enhancement...
;;;
(defstruct trivial-match-ACZ-state
  (sys nil)
  (no-more-p nil))

;;; small utility.  Side effect.
(defmacro match-ACZ-Rotate-Left (?**array ?**m*)
  "; shifts the element one bit to the left"
  ` (setf (svref ,?**array ,?**m*)
	  (* 2 (svref ,?**array ,?**m*))))

;;; Puts all repeated terms together in the list, and bashes the array (into
;;; numbers) in locations corresponding to the duplicate terms. Returns the
;;; newly grouped permutation of list.
;;; e.g. for input (a b c c c d d e f f) and #(0 0 0 0 0 0 0 0 0),
;;; this should make the array into #(0 0 3 2 1 2 1 0 2 1)."
;;;
(defmacro match-ACZ-note-repeats (mset_? array_? max_? gcd_?)
  ` (let* ((list2 nil)
	   (counter (length (the #+GCL vector #-GCL simple-vector
				 ,array_?)
			    )) )
      (declare (type list list2)
	       (type fixnum counter))
      (dolist (element ,mset_?)
	(declare (type list element))
	(let ((n (cdr element)))
	  (declare (type fixnum n))
	  (when (> n (the fixnum ,max_?))
	    (setq ,max_? n))
	  (setq ,gcd_? (gcd ,gcd_? n))
	  (if (> n 1)			; if it is repeated at all
	      (dotimes (xc n)
		(declare (type fixnum xc))
		(push (first element) list2)
		(setf counter (1-  counter))
		(setf (svref ,array_? counter)
		      (1+ xc)))
	      (progn (push (first element) list2)
		     (setf counter
			   (1- counter))
		     (setf (svref ,array_? counter) 0))))) ; this line optional
      list2))				; (if 0'd array is guaranteed)

;;; predicate. true if term is term.equational-equal some element of list"
(defmacro match-ACZ-eq-member (term_!* list_!*)
  ` (dolist ($$_term2 ,list_!*)
      (when (term-equational-equal ,term_!* $$_term2)
	(return t))))

;;; acz-state-pool

#||
(defvar .acz-state-pool. nil)

(defmacro allocate-acz-state ()
  ` (if .acz-state-pool.
	(pop .acz-state-pool.)
	(make-match-ACZ-state)))

(defmacro deallocate-acz-state (acz-state)
  `(push ,acz-state .acz-state-pool.))

(eval-when (:execute :load-toplevel)
  (dotimes (x 20) (push (make-match-ACZ-state) .acz-state-pool.)))
||#

(defmacro allocate-acz-state ()
  (make-match-ACZ-state))

#||
(defmacro deallocate-acz-state (acz-state)
  nil)
||#

#+CMU (declaim (ext:start-block match-acz-state-initialize
				match-acz-next-state
				match-acz-equal))
;;;
#+CMU
(defun test_same_term_list (x y)
  (declare (type list x y))
  (loop (when (null x) (return (null y)))
      (unless (eq (car x) (car y))
	(return nil))
    (setq x (cdr x))
    (setq y (cdr y))
    ))

;;; NOTE  this is a version for ACZ-internal use only.
;;; it simply takes care of the "from which equation" info.
;;; the input list is like
;;; ((A . 1) (B . 2) (A . 1) (A . 3))
;;; the result is like
;;; (((A . 1) . 2) ((B . 2) . 1) ((A . 3) . 1))
;;; where the A.1 means 'term a from equation 1'.
;;; and (a.1).2  means 'term a from equation 1' appears twice.

#+CMU
(defun list2multi-set-list-direct (list)
  (declare (type list list))
  (let ((ms-list nil))
    (declare (type list ms-list))
    (dolist (x list)
      (declare (type term x))
      (let ((ms-x (dolist (pr ms-list nil)
		    (when (term-equational-equal x (car pr))
		      (return pr))))) 
	(if ms-x 
	    (setf (cdr ms-x)
		  (1+ (cdr ms-x)))
	    (push (cons x 1) ms-list))
	))
    ms-list))

#+CMU
(defun list2multi-set-list (list)
  (declare (type list list))
  (if (and l2msla1 (test_same_term_list list l2msla1))
      (copy-alist l2mslv1)
  (if (and l2msla2 (test_same_term_list list l2msla2))
      (progn
	(rotatef l2msla1 l2msla2)
	(rotatef l2mslv1 l2mslv2)
	(copy-alist l2mslv1))
  (let ((res (list2multi-set-list-direct list)))
    (setq l2msla2 l2msla1  l2mslv2 l2mslv1)
    (setq l2msla1 list l2mslv1 res)
    (copy-alist res)
    ))))

(defun match-ACZ-list2multi-set (list)
  (declare (type list list)
	   ;; (optimize (speed 3) (safety 0))
	   )
  (let ((ms-list nil))
    (declare (type list ms-list))
    (dolist (x list)
      (let ((ms-elt (assoc-if #'(lambda (y)
				  (declare (type list y))
				  (and (= (the fixnum (cdr x))
					  (the fixnum (cdr y)))
				       (term-equational-equal (car y) (car x))))
			      ms-list)))
	(if ms-elt
	    (setf (cdr ms-elt)
		  (1+ (cdr ms-elt)))
	    (push (cons x 1) ms-list))))
    ms-list))

#+CMU
(defun delete-one-term
       (x y)
  (if (null y)
      'none
      (if (term-equational-equal x (caar y))
	  (cdr y)
	  (let ((last y) (rest (cdr y)))
	    (loop (when (null rest) (return 'none))
		(when (term-equational-equal x (caar rest))
		  ;; delete pattern
		  (rplacd last (cdr rest))
		  ;; new
		  (return y))
	      (setq last rest  rest (cdr rest))))
	  ))
  )

;;; check for multi-set equality
;;; uses term.equational-equal -- which can be pretty expensive
;;;
(defun match-ACZ-ms-equal (x y)
  (declare (type list x y)
	   ;; (optimize (speed 3) (safety 0))
	   )
  (block the-end
    (let ((ydone 0)
	  (ylength (length y)))
      (declare (type fixnum ydone ylength))
      ;;
      (dolist (xe x)
	(let ((xterm (car xe)) (xval (cdr xe)))
	  (declare (type term xterm)
		   (type fixnum xval))
	  (dolist (ye y (return-from the-end nil)) ; didn't find xe in y
	    (when (term-equational-equal xterm (car ye))
	      (unless (= xval (the fixnum (cdr ye)))
		(return-from the-end nil))
	      (incf ydone)
	      (return)))))		; quit the inner do-list
      (unless (= ydone ylength)
	(return-from the-end nil)))
    t))

;;;
;;; Assume that t1 is NOT a variable
;;;
(defun match-ACZ-equal (t1 t2)
  (declare (type term t1 t2)
	   ;; (optimize (speed 3) (safety 0))
	   )
  (if (term-is-applform? t2)
      (let ((op (term-method t1)))
	(declare (type method op))
	(if (method-is-of-same-operator op (term-head t2))
	    (match-ACZ-ms-equal
	     (list2multi-set-list (list-ACZ-subterms t1 op))
	     (list2multi-set-list (list-ACZ-subterms t2 op)))
	  nil))
    nil))

;;; op match-ACZ-make-term : Operator List Of Term
;;; create a single term from a collection of terms
;;;
(defun match-ACZ-make-term (op list)
  (declare (type method op)
	   (type list list)
	   ;; (optimize (speed 3) (safety 0))
	   )
  (if (null list)
      (term-make-zero op)
      (if (null (cdr list))
	  (car list)
	  (make-term-with-sort-check 
	    op (list (car list) (match-ACZ-make-term op (cdr list)))))))

;;; given an match-ACZ-state, produce a solution (system of equations
;;; which, if true, imply the original ACZ equation true) from
;;; the matrix of 'state'"
;;;
(defvar *acz-failure-pat* nil)

(defun match-ACZ-solution-from-state (state)
  ;; (declare (optimize (speed 3) (safety 0)))
  (let* ((ops (match-ACZ-state-methods state))
	 (lhs-f (match-ACZ-state-lhs-f state))
	 (lhs-v (match-ACZ-state-lhs-v state))
	 (rhs-c (match-ACZ-state-rhs-c state))
	 (rhs-f (match-ACZ-state-rhs-f state))
	 (rhs-c-sol (match-ACZ-state-rhs-c-sol state))
	 (rhs-f-sol (match-ACZ-state-rhs-f-sol state))
	 (new-sys (new-m-system))
	 (term-code 1)
	 (rhs-subterms nil)
	 (made-zero nil))
    (declare (type #-GCL simple-vector
		   #+GCL vector
		   lhs-f lhs-v rhs-c rhs-f)
	     (type list rhs-subterms)
	     (type #-GCL simple-vector
		   #+GCL vector
		   ops rhs-c-sol rhs-f-sol)
	     (type fixnum term-code))
    ;;
    (setq *acz-failure-pat* nil)
    ;; (match-ACZ-collapse-arrays-internal lhs-v 1)
    (let ((new-eqs nil))
      (dotimes (i (length lhs-v))
	(declare (type fixnum i))
	(if (< i 1)
	    nil
	    (let ((ith-var (svref lhs-v i)))
	      (setq rhs-subterms nil)
	      (setq term-code (* 2 term-code))
	      ;; (match-ACZ-collapse-one-array-internal rhs-c-sol rhs-c)
	      (dotimes (j (length rhs-c-sol))
		(declare (type fixnum j))
		(when (> (make-and (svref rhs-c-sol j)
				   term-code)
			 0)
		  (push  (car (svref rhs-c j)) rhs-subterms)))
	      ;; (match-ACZ-collapse-one-array-internal rhs-f-sol rhs-f)
	      (dotimes (j (length rhs-f-sol))
		(declare (type fixnum j))
		(when (> (make-and (svref rhs-f-sol j)
				 term-code)
		       0)
		  (push  (car (svref rhs-f j)) rhs-subterms)))
	      ;;
	      (if (null rhs-subterms)
		  (let ((zero (term-make-zero (svref ops (cdr
							   ith-var)))))
		    (when zero
		      (setq made-zero t)
		      (push (make-equation (car ith-var) zero) new-eqs)))
		  (push (make-equation (car ith-var)
				(if (cdr rhs-subterms)
				    ;; implies length is
				    ;; greater than 1 
				    (make-right-assoc-normal-form-with-sort-check
				     (svref ops (cdr ith-var))
				     rhs-subterms)
				    (first rhs-subterms)))
			new-eqs))
	      )))
      ;; note term-code is now the right thing. 
      ;; (match-ACZ-collapse-arrays-internal lhs-f 0)
      (dotimes (i (length lhs-f))
	(declare (type fixnum i))
	(let ((ith-f (svref lhs-f i)))
	  ;; (?zero (term-make-zero (svref ops (cdr ith-f))))
	  (setq rhs-subterms nil)
	  (setq term-code (* 2 term-code))
	  ;; (match-ACZ-collapse-one-array-internal rhs-c-sol rhs-c)
	  (dotimes (j (length rhs-c-sol))
	    (declare (type fixnum j))
	    (when (> (the fixnum
		       (make-and (svref rhs-c-sol j)
				 term-code))
		     0)
	      (push  (car (svref rhs-c j)) rhs-subterms)))
	  ;; (match-ACZ-collapse-one-array-internal rhs-f-sol rhs-f)
	  (dotimes (j (length rhs-f-sol))
	    (declare (type fixnum j))
	    (when (> (the fixnum (make-and (svref rhs-f-sol j)
					   term-code))
		     0)
	      (push  (car (svref rhs-f j)) rhs-subterms)))
	  (if (null rhs-subterms)
	      (let ((?zero (term-make-zero (svref ops (cdr ith-f)))))
		(if (and ?zero (method-is-of-same-operator+
				(term-head ?zero)
				(term-head (car ith-f))))
		    (progn
		      (setq made-zero t)
		      (push (make-equation (car ith-f) ?zero) new-eqs))
		    ;;
		    (progn
		      (setq *acz-failure-pat*
			    (cons (car ith-f) ?zero))
		      (setq new-eqs nil) (return nil))))
	      (let ((t1 (car ith-f))
		    (t2 (if (cdr rhs-subterms)
			    ;; implies length is greater than 1 
			    (make-right-assoc-normal-form-with-sort-check
			     (svref ops (cdr ith-f))
			     rhs-subterms)
			    (first rhs-subterms))))
		;;
		(let ((t1-head (term-head t1))
		      (t2-head (term-head t2)))
		  (if (method-is-of-same-operator+ t1-head t2-head)
		      (push (make-equation t1 t2) new-eqs)
		      (let ((minfo-1 (method-theory-info-for-matching
				      t1-head))
			    (minfo-2 (method-theory-info-for-matching
				      t2-head)))
			(if (or (test-theory
				 .z. (theory-info-code minfo-1))
				(test-theory
				 .z. (theory-info-code minfo-2)))
			    (push (make-equation t1 t2) new-eqs)
			    (progn (setq new-eqs nil)
				   (setq *acz-failure-pat* (cons t1 t2))
				   (return nil))
			    ))))
		))))
      ;;
      (if new-eqs
	  (progn
	    (dolist (eq (nreverse new-eqs))
	      (add-equation-to-m-system new-sys eq))
	    (when *match-debug* 
	      (format t "~%*** acz solution: ")
	      (print-m-system new-sys)
	      (format t "~%***")
	      )
	    (values new-sys made-zero))
	  (progn
	    (when *match-debug*
	      (format t "~%*** no possible solution in this case")
	      (print-next)
	      (princ "t1 = ") (term-print (car *acz-failure-pat*))
	      (print-next)
	      (princ "t2 = ") (term-print (cdr *acz-failure-pat*))
	      )
	    (values nil nil)))
      )))


;;; ACZ State Intialization

;;; takes a system of equations and an environment, and returns an
;;; match-ACZ-state, which is suitable for framing or passing to
;;; 'match-ACZ-next-state'" 
;;;

(defun match-ACZ-state-initialize (sys env)
  (declare (type list sys env))
  (block TOP
    (let ((eqn-number -1)
	  (sys-methods (alloc-svec (length sys)))
	  (all-lhs-vars nil)
	  (all-lhs-funs nil)
	  (all-rhs-constants nil)
	  (all-rhs-funs nil)
	  (*print-circle* nil))
      (declare (type fixnum eqn-number)
	       #-GCL (type simple-vector sys-methods)
	       #+GCL (type vector sys-methods)
	       (type list all-lhs-vars all-lhs-funs all-rhs-constants
		     all-rhs-funs))
      (dolist (equation sys)
	(setf eqn-number
	      (1+ eqn-number))
	(let* ((lhs-1 (equation-t1 equation))
	       (rhs-1 (equation-t2 equation))
	       (lh-meth (term-method lhs-1))
	       (rhs-meth (if (and (term-is-applform? rhs-1)
				  (not (term-is-builtin-constant? rhs-1)))
			     (term-method rhs-1)
			     nil))
	       (lhs-2 (list-ACZ-subterms lhs-1 lh-meth))
	       (rhs-2
		(if (and rhs-meth
			 (method-is-AC-restriction-of rhs-meth lh-meth))
		    (list-ACZ-subterms rhs-1 rhs-meth)
		    (list rhs-1)))
	       (lhs-vars nil)
	       (lhs-constants nil)
	       (lhs-funs nil)
	       (rhs-constants nil)
	       (rhs-funs nil)
	       )
	  (declare (type term rhs-1 rhs-1)
		   (type method lh-meth)
		   (type (or null method) rhs-meth)
		   (type list lhs-2 rhs-2 lhs-vars lhs-constants lhs-funs
			 rhs-constants rhs-funs))
	  ;;
	  (setf (svref sys-methods eqn-number) lh-meth)
	  ;; quick failure cases of AC do Not apply to ACZ
	  ;; build lhs- vars/funs/constants
	  (dolist (term lhs-2)
	    ;; for each subterm of lhs
	    ;; note: unit elements are already eliminated from lhs-2.
	    ;;
	    (cond ((term-is-variable? term)
		   (let ((image (if env (environment-image env term) term)))
		     (cond ((null image) 
			    (push (cons term eqn-number) lhs-vars))
			   ((term-is-variable? image)
			    (push (cons image eqn-number) lhs-vars))
			   ((term-is-constant? image)
			    (push (cons image eqn-number) lhs-constants))
			   ((method-is-AC-restriction-of lh-meth
							 (term-method image))
			    (dolist (term2 (list-ACZ-subterms
					    image (term-head image)))
			      (cond ((term-is-variable? term2)
				     (push (cons term2 eqn-number)
					   lhs-vars))
				    ((term-is-constant? term2)
				     (push (cons term2 eqn-number)
					   lhs-constants))
				    (t (push (cons term2 eqn-number)
					     lhs-funs)))))
			   (t (push (cons image eqn-number) lhs-funs)))))
		  ((term-is-constant? term)
		   #|| term can never be a unit. <- list-acz-subterms.
		   (unless (term-is-zero-for-method term lh-meth)
		      (push (cons term eqn-number) lhs-constants))
		   ||#
		   (push (cons term eqn-number) lhs-constants)
		   )
		  (t (push (cons term eqn-number) lhs-funs))))
	  ;;
	  ;; now that the lhs is partitioned - lets play with the rhs
	  ;;
	  (dolist (term rhs-2)
	    (cond ((term-is-variable? term)
		   (push (cons term eqn-number) rhs-constants))
		  ((term-is-constant? term)
		   (unless (term-is-zero-for-method term lh-meth)
		     (let ((new (delete-one-term term lhs-constants)))
		       (if (eq 'none new)
			   (push (cons term eqn-number) rhs-constants)
			   (if (eq new :never-match)
			       (if lhs-vars
				   (push (cons term eqn-number) rhs-constants)
				   (return-from TOP (values nil t)))
			       (setq lhs-constants new))))))
		  (t (let ((new (delete-one-term term lhs-funs)))
		       (if (eq 'none new)
			   (push (cons term eqn-number) rhs-funs)
			   (if (eq new :never-match)
			       (if lhs-vars
				   (push (cons term eqn-number) rhs-funs)
				   (return-from TOP (values nil t)))
			       (setq lhs-funs new)))))))
	  ;; now there are no duplicates (things appearing on both sides)
	  (let ((lhs-c-count (length lhs-constants))
		(lhs-f-count (length lhs-funs))
		(lhs-v-count (length lhs-vars))
		(rhs-c-count (length rhs-constants))
		(rhs-f-count (length rhs-funs))
		)
	    (declare (type fixnum lhs-c-count lhs-f-count lhs-v-count
			   rhs-c-count rhs-f-count))
	    ;; check trivial failure conditions
	    (when (or (> lhs-c-count 0)	; a const without anything to match it
		      (and (< lhs-v-count 1) ; no variables remain on lhs
			   (> rhs-c-count 0)) ; and constants remain on rhs
		      (> lhs-f-count rhs-f-count)) ; too many funs to match
	      ;; this assumption may be dubius in ACZ --- can arbitrary 
	      ;; funs eventually reduce to identity?
	      (return-from TOP (values nil t)))	; FAIL most miserably
	    (setq all-lhs-funs (nconc lhs-funs all-lhs-funs))
	    (setq all-lhs-vars (nconc lhs-vars all-lhs-vars))
	    (setq all-rhs-constants (nconc rhs-constants all-rhs-constants))
	    (setq all-rhs-funs (nconc rhs-funs all-rhs-funs)))))
      ;; we are now done with all equations.
      ;; NOTE that we have now gathered all equations into one giant morass
      (cond ((and (null all-lhs-funs)	; nothing left, all formulas removed
		  (null all-lhs-vars))
	     (if (and (null all-rhs-constants) ; this is rare
		      (null all-rhs-funs))
		 (return-from TOP (values (make-trivial-match-ACZ-state 
					   :sys (new-m-system)) nil))
		 (return-from TOP (values nil t))))
	    ;; maybe check for more simple cases, like one-var vs the world.
	    ((and *use-one-var-opt*
		  (null all-lhs-funs)	; only one var left on lhs
		  (null (cdr all-lhs-vars)))
	     (let ((fresh-sys (new-m-system)))
	       (add-equation-to-m-system fresh-sys
					 (make-equation
					  (caar all-lhs-vars)
					  (match-ACZ-make-term
					   (svref sys-methods
						     (cdar all-lhs-vars))
					   (nconc all-rhs-constants
						  all-rhs-funs))))
	       (return-from TOP (values (make-trivial-match-ACZ-state :sys fresh-sys) 
					nil))))
	    (t
	     (let* ((lhs-f-count (length all-lhs-funs))
		    (lhs-v-count (1+ (length all-lhs-vars))) ; note this is "wrong"
		    ;; (lhs-v-count (length all-lhs-vars))
		    (rhs-c-count (length all-rhs-constants))
		    (rhs-f-count (length all-rhs-funs))
		    (lhs-f-r (alloc-svec-fixnum lhs-f-count))
		    (lhs-v-r (alloc-svec-fixnum lhs-v-count))
		    (rhs-c-r (alloc-svec-fixnum rhs-c-count))
		    (rhs-f-r (alloc-svec-fixnum rhs-f-count))
		    (LHS-f-ms (match-ACZ-list2multi-set all-lhs-funs)) ; expensive.
		    (LHS-v-ms (match-ACZ-list2multi-set all-lhs-vars)) ; expensive.
		    (RHS-c-ms (match-ACZ-list2multi-set all-rhs-constants)) ; expensive.
		    (RHS-f-ms (match-ACZ-list2multi-set all-rhs-funs)) ; expensive.
		    (l-f-m 0)		; TCW 14 Mar 91 mods associated with this var
		    (l-v-m 0)		; note this is not used
		    (r-m 0)
		    (l-gcd (or (cdar lhs-f-ms) (cdar lhs-v-ms) 1))
		    (r-gcd (or (cdar rhs-f-ms) (cdar rhs-c-ms) 1))
		    (LHS-f-list (match-ACZ-note-repeats lhs-f-ms lhs-f-r l-f-m l-gcd))

		    (LHS-v-list  (cons (cons 'if-this-appears-youve-lost 999) 
				       (match-ACZ-note-repeats lhs-v-ms lhs-v-r l-v-m l-gcd)))

		    (RHS-c-list (match-ACZ-note-repeats rhs-c-ms rhs-c-r r-m r-gcd))
		    (RHS-f-list (match-ACZ-note-repeats rhs-f-ms rhs-f-r r-m r-gcd))
		    (LHS-f (make-array lhs-f-count :initial-contents lhs-f-list))
		    (LHS-v (make-array lhs-v-count :initial-contents lhs-v-list))
		    (RHS-c (make-array rhs-c-count :initial-contents rhs-c-list))
		    (RHS-f (make-array rhs-f-count :initial-contents rhs-f-list))
		    (RHS-c-max (expt2 (1- lhs-v-count)))
		    (RHS-f-max (expt2 (+ -1 lhs-v-count lhs-f-count)))
		    (RHS-full-bits (- (expt2 (+ lhs-v-count lhs-f-count)) 2))
		    (rhs-c-sol (alloc-svec-fixnum rhs-c-count))
		    (rhs-f-sol (alloc-svec-fixnum rhs-f-count))
		    (rhs-c-compat (alloc-svec-fixnum rhs-c-count))
		    (rhs-f-compat (alloc-svec-fixnum rhs-f-count))
		    (dummy-bit 1)	; to save a whole bunch of expt'ing
		    (lhs-r-mask 0)
		    (state (make-match-ACZ-state))
		    )
	       (declare (type #-GCL simple-vector
			      #+GCL vector
			      lhs-f-r lhs-v-r rhs-c-r rhs-f-r
			      rhs-c-sol rhs-f-sol
			      rhs-c-compat rhs-f-compat)
			(type #-GCL simple-vector
			      #+GCL vector
			      lhs-f lhs-v rhs-c rhs-f)
			(type fixnum
			      rhs-c-max rhs-f-max rhs-full-bits
			      lhs-f-count lhs-v-count rhs-c-count rhs-f-count
			      dummy-bit lhs-r-mask l-gcd r-gcd l-f-m r-m))
	       ;;(declare (ignore l-v-m)) not strictly true
	       ;; one more easy failure check
	       ;; TCW 14 Mar 91 need to restrict this for ACZ
	       (when (or (> l-f-m r-m)	; a lhs item is repeated more than any rhs
			 (not (integerp (/ r-gcd l-gcd))))
		 ;; (deallocate-acz-state state)
		 (return-from TOP (values nil t))) ; FAIL most miserably
	       ;; NOW, get down to the real work....
	       ;; setup the repeat mask (first of v's)
	       (dotimes (j lhs-v-count)
		 (declare (type fixnum j))
		 (when (> (the fixnum (svref lhs-v-r j)) 1)
		   (setq lhs-r-mask (make-or lhs-r-mask dummy-bit))
		   (setq dummy-bit (* 2 dummy-bit))))
	       ;; note dummy-bit might not be 1 here...
	       (dotimes (j lhs-f-count) ; (then of f's)
		 (declare (type fixnum j))
		 (when (> (the fixnum (svref lhs-f-r j)) 1)
		   (setq lhs-r-mask (make-or lhs-r-mask dummy-bit))
		   (setq dummy-bit (* 2 dummy-bit))))
	       ;; now setup the compatibility bitvectors (for rhs-c)
	       (dotimes (i rhs-c-count)
		 (declare (type fixnum i))
		 (setq dummy-bit 1)
		 (let ((my-repeat-count (svref rhs-c-r i)))
		   (declare (fixnum my-repeat-count))
		   (dotimes (j lhs-v-count)
		     (declare (type fixnum j))
		     (when (and (= (the fixnum (cdr (svref rhs-c i)))
				   (the fixnum (cdr (svref lhs-v j))))
				;; both are from same equation, AND
				(or (= (the fixnum (svref lhs-v-r j))
				       my-repeat-count)
				    ;; the right repetition number OR 0
				    (= (the fixnum (svref lhs-v-r j))
				       0)))
		       (setf (svref rhs-c-compat i)
			     (make-or (svref rhs-c-compat i)
				      dummy-bit)))
		     (setq dummy-bit (* 2 dummy-bit)))))
	       ;; now setup the compatibility bitvectors (for rhs-f)
	       (dotimes (i rhs-f-count)
		 (declare (type fixnum i))
		 (setq dummy-bit 1)
		 (let ((my-repeat-count (svref rhs-f-r i)))
		   (declare (fixnum my-repeat-count))
		   (dotimes (j lhs-v-count)
		     (declare (type fixnum j))
		     (when (and (= (the fixnum (cdr (svref rhs-f i)))
				   (the fixnum (cdr (svref lhs-v j))))
				;; both are from same equation, AND
				(or (= (the fixnum (svref lhs-v-r j))
				       my-repeat-count)
				    (= (the fixnum (svref lhs-v-r j))
				       0)))
		       (setf (svref rhs-f-compat i)
			     (make-or (svref rhs-f-compat i)
				      dummy-bit)))
		     (setq dummy-bit (* 2 dummy-bit)))
		   ;; now lhs vars are taken care of, we need to deal with funs
		   (dotimes (j lhs-f-count)
		     (declare (type fixnum j))
		     ;; for now, ignore repetition of funs (can be slower)
		     (when (and (= (the fixnum (cdr (svref rhs-f i)))
				   (the fixnum (cdr (svref lhs-f j))))
				;; both are from same equation, AND
				(possibly-matches (car (svref lhs-f j))
						  (car (svref rhs-f i))))
		       (setf (svref rhs-f-compat i)
			     (make-or (svref rhs-f-compat i)
				      dummy-bit)))
		     (setq dummy-bit (* 2 dummy-bit)))))
	       ;; and now set up the initial state to a legal one (the smallest
	       ;; legal one) 
	       ;; by just rotating the bit until it make-and's with the
	       ;; compatibility vector 
	       (dotimes (i rhs-c-count)
		 (declare (type fixnum i))
		 (setq dummy-bit 1)
		 (if (and (= i 0) (= rhs-f-count 0))
		     (setf (svref rhs-c-sol 0) 1)
		     (let ((my-compat (svref rhs-c-compat i)))
		       (declare (type fixnum my-compat))
		       (do ()
			   ((> dummy-bit rhs-c-max) 
			    (progn ;; (deallocate-acz-state state)
				   (return-from TOP (values nil t))))
			 (unless (zerop (make-and dummy-bit my-compat))
			   (setf (svref rhs-c-sol i) dummy-bit)
			   (return))
			 (setq dummy-bit (* 2 dummy-bit))))))
	       (dotimes (i rhs-f-count)
		 (declare (type fixnum i))
		 (setq dummy-bit 1)
		 (if (= i 0)
		     (setf (svref rhs-f-sol 0) 1)
		     (let ((my-compat (svref rhs-f-compat i)))
		       (declare (type fixnum my-compat))
		       (do ()
			   ((> dummy-bit rhs-f-max)
			    (progn
			      ;; (deallocate-acz-state state)
			      (return-from TOP (values nil t))))
			 (unless (zerop (make-and dummy-bit my-compat))
			   (setf (svref rhs-f-sol i) dummy-bit)
			   (return))
			 (setq dummy-bit (* 2 dummy-bit))))))

	       ;; initialize the mask -
	       (if (= rhs-f-count 0)
		   (setf (match-ACZ-state-LHS-mask state) 0)
		   (let ((temp 0))
		     (declare (type fixnum temp))
		     (dotimes (s rhs-c-count)
		       (declare (type fixnum s))
		       (setq temp (make-or temp
					   (svref rhs-c-sol s))))
		     (setf (match-ACZ-state-LHS-mask state) temp)))

	       ;; and now stuff the state full of information, and return it.
	       (setf (match-ACZ-state-methods state) sys-methods)
	       (setf (match-ACZ-state-LHS-f state) lhs-f)
	       (setf (match-ACZ-state-LHS-v state) lhs-v)
	       (setf (match-ACZ-state-RHS-c state) rhs-c)
	       (setf (match-ACZ-state-RHS-f state) rhs-f)
	       (setf (match-ACZ-state-LHS-f-r state) lhs-f-r)
	       (setf (match-ACZ-state-LHS-v-r state) lhs-v-r)
	       (setf (match-ACZ-state-RHS-c-r state) rhs-c-r)
	       (setf (match-ACZ-state-RHS-f-r state) rhs-f-r)
	       ;; (setf (match-ACZ-state-LHS-mask state) 0)
	       (setf (match-ACZ-state-LHS-f-mask state) 0)
	       (setf (match-ACZ-state-LHS-r-mask state) lhs-r-mask)
	       (setf (match-ACZ-state-RHS-c-sol state) rhs-c-sol)
	       (setf (match-ACZ-state-RHS-c-max state) rhs-c-max)
	       (setf (match-ACZ-state-RHS-f-sol state) rhs-f-sol)
	       (setf (match-ACZ-state-RHS-f-max state) rhs-f-max)
	       (setf (match-ACZ-state-RHS-full-bits state) rhs-full-bits)
	       (setf (match-ACZ-state-RHS-c-compat state) rhs-c-compat)
	       (setf (match-ACZ-state-RHS-f-compat state) rhs-f-compat)
	       (setf (match-ACZ-state-LHS-c-count state) 0)
	       (setf (match-ACZ-state-LHS-f-count state) lhs-f-count)
	       (setf (match-ACZ-state-LHS-v-count state) lhs-v-count)
					; off 1+ intentionally 
	       (setf (match-ACZ-state-RHS-c-count state) rhs-c-count)
	       (setf (match-ACZ-state-RHS-f-count state) rhs-f-count)
	       (setf (match-ACZ-state-no-more state) nil)
	       (setf (match-ACZ-state-acz-state-p state) 'acz-state)
	       ;;
	       (when *match-debug*
		 (format t "~&acz-init: state=~&")
		 (match-ACZ-unparse-match-ACZ-state state))
	       ;;
	       (values state nil)))))))

#||

(defun match-ACZ-state-initialize (sys env)
  (match-AC-state-initialize sys env :have-unit))
||#
  
(defun match-ACZ-next-state-sub (state)
  (do* ((m 0)				; only initialize these vars 
	(rhs-c-sol (match-ACZ-state-rhs-c-sol state))
	(rhs-c-max (match-ACZ-state-rhs-c-max state))
	(rhs-c-count (match-ACZ-state-rhs-c-count state))
	(rhs-c-compat (match-ACZ-state-rhs-c-compat state))
	(lhs-r-mask (match-ACZ-state-lhs-r-mask state)))
       (nil)				; forever
    (declare (type #+GCL vector #-GCL simple-vector rhs-c-compat rhs-c-sol)
	     (type fixnum lhs-r-mask rhs-c-count rhs-c-max m))
    (cond ((>= m rhs-c-count)		; no next row
	   (setf (match-ACZ-state-no-more state) T)
	   (return))
	  ((< m 0)			; no tests up here - could cut search here
	   (let ((temp 0))		; the empty bitvector
	     (declare (type fixnum temp))
	     (dotimes (s rhs-c-count)
	       (declare (type fixnum s))
	       (setq temp (make-or temp (svref rhs-c-sol s))))
	     (setf (match-ACZ-state-LHS-mask state) temp)
	     (return)))
	  ((< (the fixnum (svref rhs-c-sol m)) rhs-c-max)
	   (match-ACZ-Rotate-Left rhs-c-sol m)
	   (when (and			; this is a compatible
					; position for this bit 
		  (> (make-and (svref rhs-c-sol m)
			       (svref rhs-c-compat m))
		     0)
		  ;; either this isnt a repeated term
		  (or (zerop (make-and (svref rhs-c-sol m)
				       lhs-r-mask))
		      ;; or it is, and its upper neighbor is home
		      (and (< (1+ m) rhs-c-count)
			   (= (* 2 (the fixnum (svref rhs-c-sol m)))
			      (the fixnum (svref rhs-c-sol (1+ m)))))))
	     (setq m (1- m))))		; then this row is ok, else redo this row
	  (t				; this row (m) is already maxed
	   (setf (svref rhs-c-sol m) 1)	; reset this row
	   (setq m (1+ m))))))		; go to next row

;;; ACZ Next State

(defun match-ACZ-next-state (state)
  (if (trivial-match-ACZ-state-p state)
      (if (trivial-match-ACZ-state-no-more-p state)
	  (values nil nil t)
	(progn 
	  (setf (trivial-match-ACZ-state-no-more-p state) t)
	  (values (trivial-match-ACZ-state-sys state) nil nil)))
    (if (not (match-ACZ-state-p state))    
	(progn (format t "~& match-ACZ-Next-State given non match-ACZ-state:~A~&" state)
	       (values nil t nil))
      (let ((sys nil)
	    (no-more (match-acz-state-no-more state))
	    (zero nil))
	(if no-more
	    (let ((zeros (pop (match-acz-state-zero-matches state))))
	      (if zeros
		  (values zeros state nil)
		(values nil nil t)))
	  (progn
	    (loop
	      (multiple-value-setq (sys no-more zero)
		(match-acz-next-state-aux state))
	      (when no-more (return))
	      (when (not zero) (return))
	      (push sys (match-acz-state-zero-matches state))
	      )
	    (if no-more
		(match-acz-next-state state)
	      (values sys state nil)
	      )
	    )
	  )
      ))))
	  
(defun match-acz-next-state-aux (state)
  (when *match-debug*
    (format t "~&** ACZ next state"))
  (if (match-ACZ-state-no-more state)
      (progn
	;; (deallocate-acz-state state)
	(values nil t nil)		; there are no more solutions - so fail
	)
    (do* ((n 0) 
	  (rhs-f-sol (match-ACZ-state-rhs-f-sol state))
	  (rhs-f-max (match-ACZ-state-rhs-f-max state))
	  (rhs-f-compat (match-ACZ-state-rhs-f-compat state))
	  (rhs-f-count (match-ACZ-state-rhs-f-count state))
	  ;;   (rhs-full-bits (match-ACZ-state-rhs-full-bits state)) ;@@
	  (lhs-r-mask (match-ACZ-state-lhs-r-mask state))
	  (made-zero nil)
	  )
	(nil)				; do forever
      (declare (type fixnum n rhs-f-count rhs-f-max lhs-r-mask)
	       (type #+GCL vector #-GCL simple-vector
		     rhs-f-sol rhs-f-compat))
      (cond ((< n 0)
	     (let ((temp (match-ACZ-state-LHS-mask state)))
	       (declare (type fixnum temp))
	       ;;acz (make-or (- (expt2 (ACZ-stat-lhs-v-count state)) 1))
	       (dotimes (s rhs-f-count)
		 (declare (type fixnum s))
		 (setq temp (make-or temp (svref rhs-f-sol s))))
	       (let ((sol nil))
		 (multiple-value-setq (sol made-zero)
		   (match-ACZ-solution-from-state state))
		 (if sol
		     (return (values sol nil made-zero))
		   (return (match-acz-next-state-aux state))))))
	    ;;
	    ((>= n rhs-f-count)		; no next row
	     (match-ACZ-next-state-sub state)
	     (if (match-ACZ-state-no-more state)
		 (if (and (= 0 (the fixnum
				 (match-ACZ-state-LHS-f-count state)))
			  (<= 1 (the fixnum
				  (match-ACZ-state-LHS-v-count state)))
			  (= 0 (the fixnum
				 (match-ACZ-state-RHS-c-count state)))
			  (= 0 (the fixnum
				 (match-ACZ-state-RHS-f-count state)))
			  ;; TCW 14 Mar 91 vaguely plausible
			  (let ((lhs-v (match-ACZ-state-lhs-v state))
				(ops (match-ACZ-state-methods state)))
			    (declare (type #+GCL vector
					   #-GCL simple-vector
					   lhs-v ops))
			    (dotimes (i (length lhs-v) t)
			      (declare (type fixnum i))
			      (if (< i 1) nil
				(unless (sort<=
					 (term-sort
					  (car (theory-zero
						(method-theory (svref
								ops
								(cdr
								 (svref
								  lhs-v
								  i)))))))
					 (term-sort (car (svref lhs-v i))))
				  (return nil))))))
		     (let ((sol nil))
		       (multiple-value-setq (sol made-zero)
			 (match-acz-solution-from-state state))
		       (if sol
			   (return (values sol nil made-zero))
			 (return (match-acz-next-state-aux state))))
		   (progn
		     ;; failed at f-level
		     ;; (deallocate-acz-state state)
		     (return (values nil t nil))))
	       (setq n (1- n)))
	     )
	    ((< (the fixnum (svref rhs-f-sol n)) rhs-f-max)
	     (match-ACZ-Rotate-Left rhs-f-sol n)
	     (when (and			; this is a compatible position for this bit
		    (> (make-and (svref rhs-f-sol n)
				 (svref rhs-f-compat n))
		       0)
		    ;; either this isnt a repeated term
		    (or (= 0
			   (the fixnum (make-and (svref rhs-f-sol n)
						 lhs-r-mask)))
			;; or it is, and its upper neighbor is home
			(and (< (1+ n) rhs-f-count)
			     (= (the fixnum (* 2 (svref rhs-f-sol n)))
				(the fixnum (svref rhs-f-sol (1+ n)))))))
	       (setq n (1- n))))	; then this row is ok, else redo 
	    
	    (t				; this row (n) is already maxed
	     (setf (svref rhs-f-sol n) 1) ; reset this row to one
	     (setq n (1+ n)))))))

#||
(defun match-ACZ-next-state (state)
  (match-AC-next-state state))
||#

#+CMU (declaim (ext:end-block))

;; printout of important parts of ACZ state.
(defun match-ACZ-unparse-match-ACZ-state (ACZ-st)
  (format t "~&no more=~A~%" (match-ACZ-state-no-more ACZ-st))
  (format t "~&operators: ~&")
  (map nil #'print-chaos-object(match-ACZ-state-methods ACZ-st))
  (format t "~&RHS-f: ~&")
  (map nil #'print-chaos-object (match-ACZ-state-RHS-f ACZ-st))
  (format t "~&RHS-c: ~&")
  (map nil #'print-chaos-object (match-ACZ-state-RHS-c ACZ-st))
  (format t "~&LHS-v: ~&")
  (map nil #'print-chaos-object (match-ACZ-state-LHS-v ACZ-st)) 
  (format t "~&LHS-f: ~&")
  (map nil #'print-chaos-object (match-ACZ-state-LHS-f ACZ-st))
  (format t "~& rhs-c-count=~A, rhs-f-count=~A~&"
	  (match-ACZ-state-RHS-c-count ACZ-st) 
	  (match-ACZ-state-RHS-f-count ACZ-st))
  (format t "~& lhs-c-count=~A, lhs-f-count=~A, lhs-v-count=~A~%"
	  (match-ACZ-state-LHS-c-count ACZ-st) 
	  (match-ACZ-state-LHS-f-count ACZ-st) 
	  (match-ACZ-state-LHS-v-count ACZ-st))
  (let ((*print-base* 2)) ; these be bitvectors, print them as such
    (format t "-------------------~%rhs-c-sol= ~A~&rhs-f-sol=~A~&"
	    (match-ACZ-state-RHS-c-sol ACZ-st) (match-ACZ-state-RHS-f-sol ACZ-st))
    (format t "~& rhs-c-max=~A, rhs-f-max=~A, rhs-full-bits=~A~&"
	    (match-ACZ-state-RHS-c-max ACZ-st) 
	    (match-ACZ-state-RHS-f-max ACZ-st)
	    (match-ACZ-state-RHS-full-bits ACZ-st))
    (format t "~& rhs-c-compat=~A, rhs-f-compat=~A~&"
	    (match-ACZ-state-RHS-c-compat ACZ-st) 
	    (match-ACZ-state-RHS-f-compat ACZ-st))
    (format t "~& rhs-c-r=~A, rhs-f-r=~A~&"
	    (match-ACZ-state-RHS-c-r ACZ-st) 
	    (match-ACZ-state-RHS-f-r ACZ-st))
    (format t "~& lhs-f-r=~A, lhs-v-r=~A~&"
	    (match-ACZ-state-LHS-f-r ACZ-st) 
	    (match-ACZ-state-LHS-v-r ACZ-st))
    (format t "~& lhs-mask=~A~%"
	    (match-ACZ-state-LHS-mask ACZ-st))
    (terpri)
    (format t "~& lhs-f-mask=~A~%"
	    (match-ACZ-state-LHS-f-mask ACZ-st))
    (format t "~& lhs-r-mask=~A~%"
	    (match-ACZ-state-LHS-r-mask ACZ-st))
    ))

(defun match-ACZ-trivial-unparse (state)
  (let ((sys (trivial-match-ACZ-state-sys state))
	(no-more-p (trivial-match-ACZ-state-no-more-p state)))
    sys
    (format t "~% acz-unparse-trivial no-more-p = ~A~%" no-more-p)
    )
  )

(defun match-ACZ-args-nss (x) (match-ACZ-unparse-match-ACZ-state (car x)) (terpri))
(setf (get 'match-ACZ-next-state-sub 'print-args) 'match-ACZ-args-nss)

;;; EOF
