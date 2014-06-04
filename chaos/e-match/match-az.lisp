;;;-*- Mode:Lisp; Syntax:CommonLisp; Package:CHAOS -*-
;;; $Id: match-az.lisp,v 1.2 2007-04-03 06:46:14 sawada Exp $
(in-package :chaos)
#|==============================================================================
				  System:Chaos
				 Module:e-match
			       File:match-az.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDURES for AZ Matching =================================================
;;; BASED ON matcher of OBJ3 Interpreter of SRI International:
;;; Copyright 1988,1991 SRI International.  All right reserved.

;;; ASSOCIATIVE with Identity STATE

(defstruct (match-az-state (:constructor create-match-az-state
					 (size method sys)))
  (size 0 :type fixnum :read-only t)
  (method nil :read-only t)
  sys					; array[match-eq-comp]
  no-more
  (zero-matches nil))

#||
(deftype match-az-state () 'list)
(defmacro create-match-az-state (size____ method____ sys____)
  `(list ,size____ ,method____ ,sys____ nil))

(defmacro match-az-state-size (a???) `(the fixnum (car ,a???)))
(defmacro match-az-state-method (???a) `(the method (cadr ,???a)))
(defmacro match-az-state-sys (_??a?) `(caddr ,_??a?))
(defmacro match-az-state-no-more (a_???) `(the (or null t) (cadddr ,a_???)))

||#

;;;
;;; simplify the left symbols and the right symbols. Returns the modified
;;; list of terms
;;; example: (a,x,c,z,d,c) == (a,b,b,b,c,c,c,c) is simplified into
;;;            (x,c,z,d)   ==   (b,b,b,c,c,c)
;;; Z: notice that a variable  appearing in the right hand side
;;; should never be simplified. It  will be the case
;;; if the right hand side is always renamed before matching ...
;;;
(declaim (inline match-associative-id-simplify))

(#-GCL defun #+GCL si:define-inline-function
       match-associative-id-simplify (sub1 sub2)
  (declare (type list sub1 sub2))
  (do ((t1 (car sub1) (car sub1))
       (t2 (car sub2) (car sub2)))
      ((or (not sub1) (not sub2)
	   (term-is-variable? t1)
	   (not (term-equational-equal t1 t2))))
    (pop sub1)
    (pop sub2))
  (setq sub1 (nreverse sub1) 
	sub2 (nreverse sub2))
  (do ((t1 (car sub1) (car sub1))
       (t2 (car sub2) (car sub2)))
      ((or (not sub1) (not sub2)
	   (term-is-variable? t1)
	   (not (term-equational-equal t1 t2))))
    (pop sub1)
    (pop sub2))
  (values (nreverse sub1) (nreverse sub2)))

;;; initialize the first state associated with sub1 sub2
  
(declaim (inline match-associativity-id-set-eq-state))

(#-GCL defun #+GCL si:define-inline-function
       match-associativity-id-set-eq-state (sub1 sub2)
  (declare (type list sub1 sub2))
  (let* ((sz1 (length sub1))
	 (comp (alloc-svec-fixnum (if (= 0 (the fixnum sz1))
				      0
				      (- (the fixnum sz1) 1)))))
    (declare (type fixnum sz1)
	     (type #+GCL vector
		   #-GCL simple-vector comp))
    (values (make-match-equation-comp 
	     sz1 
	     (make-array (the fixnum (length sub1)) :initial-contents sub1)
	     (make-array (the fixnum (length sub2)) :initial-contents sub2)
	     comp))))

;;; op match-AZ-make-term : Operator Array[Term] Int Int -> Term
;;; create a single term from a collection of terms
(declaim (inline match-az-make-term))

(#-GCL defun #+GCL si:define-inline-function
       match-AZ-make-term (method vect first last)
  (declare (type method method)
	   (type fixnum first last)
	   (type #+GCL vector #-GCL simple-vector vect)
	   (values term))
  (cond
   ((= first last) (values (term-make-zero method) t))
   ((= (1+ first) last) (values (%svref vect first) nil))
   (t (let ((res (%svref vect (1- last))))
	(do ((i (- last 2) (1- i)))
	    ((< i first) res)
	  (declare (type fixnum i))
	  (unless (term-is-zero-for-method (%svref vect i) method)
	    (setq res (make-term-with-sort-check 
		       method (list (%svref vect i) res)))))
	(values res nil)))))

;;; try to increase with respect with the lexicographical order
;;; on the arrays of integer the integer array "comp". These are
;;; the following constaints:
;;; 1) the elements of the array are all different and ordered in 
;;; pdl addition:  "weakly"
;;; increasing order: example (2 3 4 6 8)
;;; 2) the grastest element of the array in LESS OR EQUAL to "max"
;;; Returns true iff one have succeded to increment.
;;;
(declaim (inline match-az-try-increase-lexico))

(#-GCL defun #+GCL si:define-inline-function
       match-AZ-try-increase-lexico (comp max)
  (declare (type #+GCL vector #-GCL simple-vector comp)
	   (type fixnum max)
	   (values (or null t)))
  (let ((lim (the fixnum (1- (the fixnum (length comp))))))
    (declare (type fixnum lim))
    (do ((i lim (- i 1)))
	((< i 0) nil)
      (declare (type fixnum i))
      (let ((x (%svref comp i)))
	(declare (type fixnum x))
	(when (< x max)
	  (setf (%svref comp i) (1+ x))
	  (do ((j (1+ i) (1+ j)))
	      ((< lim j))
	    (declare (type fixnum j))
	    (setf (%svref comp j) (1+ x)))
	  (return t))))))

;;; modify the match-AZ-state "AZ-st" by  incrementing the state local to each
;;; equation of the system in a "variable basis numeration" way
;;;
(declaim (inline increment-the-match-az-state))

(#-GCL defun #+GCL si:define-inline-function
       increment-the-match-AZ-state (AZ-st)
  (declare (type match-az-state az-st))
  (block the-end
    (let ((sz (match-AZ-state-size AZ-st))
	  (sys (match-AZ-state-sys AZ-st)))
      (declare (type fixnum sz))
      (let ((k 0) eq-comp)
	(declare (type fixnum k))
	(while (> sz k)
	  (setq eq-comp (%svref sys k))
	  (when (match-AZ-try-increase-lexico
		 (match-equation-comp-comp eq-comp)
		 (length (match-equation-comp-right eq-comp)))
	    ;; note that match-AZ-try-increase-lexico modify in this case
	    ;; the  "comp"  of the current equation.
	    ;; After that the previous composant are reset like in
	    ;; 599 -> 600
	    (match-AZ-reset-equation-comp sys k)
	    (return-from the-end (values nil)))
	    ;;otherwise, try to increase the next equation
	  (incf k)))
      ;; this "normal" exit of the loop means that none of the
      ;; state has been increased so there is no more state
      (setf (match-AZ-state-no-more AZ-st) t))))

;;; reset the comp of "eq-comp" to his initial value i.e. (1,1,1,1,1)
;;; op match-AZ-reset-comp: EquationComp -> EquationComp~
(declaim (inline match-az-reset-comp))

(#-GCL defun #+GCL si:define-inline-function
       match-AZ-reset-comp (eq-comp)
  (let ((comp (match-equation-comp-comp eq-comp)))
    (declare (type #+GCL vector #-GCL simple-vector comp))
    (dotimes-fixnum (x (1- (the fixnum
			     (match-equation-comp-sz-left eq-comp))))
					; x = 0,...,sz-left - 2
       (setf (%svref comp x) 0))))

;;; modifies the array "sys" of "equation-comp" in such a way that
;;; all the comp array are reset provide that they rank in "sys"
;;; is less (strictly) than K.

(declaim (inline match-az-reset-equation-comp))

(#-GCL defun #+GCL si:define-inline-function
       match-AZ-reset-equation-comp (sys K)
  (declare (type #+GCL vector #-GCL simple-vector sys))
  (dotimes-fixnum (i K)				; i = 0,...,K-1 
    (match-AZ-reset-comp (%svref sys i))))

;;; INITIALIZATION

;;; Initialize an associative state. Suppose that for any equation
;;; t1 == t2 of "sys", t1 and t2 are not E-equal.

;;; 0) take the associative normal form (at the first level) 
;;;    of each term of the system
;;; 1) it checks if the top symbols of each equation of the system 
;;;     have the same (associative) head function.
;;; 2) it checks if length(Left[i]) =< length(Right[i])
;;; 3) it simplifies all the similar term in Left[i] and Right[i]
;;;    at their left or right extremity
;;; 4) initialize left-state
;;;
(defun match-AZ-state-initialize (sys env)
  (declare (type list sys env))
  (block no-match
    (let* ((dim (size-of-m-system sys))
	   (assoc-sys (alloc-svec dim))
	   (meth nil)
	   (i 0)
	   (az-state nil))
      (declare (type fixnum dim i)
	       (type #+GCL vector #-GCL simple-vector assoc-sys))
      (dolist (equation (m-system-to-list sys))
	(let ((t1 (equation-t1 equation))
	      (t2 (equation-t2 equation)))
	  (setq meth (term-method t1))
	  (let ((sub1 (list-assoc-id-subterms t1 meth))
		(sub1add nil)
		(sub2 (list-assoc-id-subterms t2 meth)))
	    (declare (type list sub1 sub1add sub2))
	    (dolist (val sub1)
	      (if (term-is-variable? val)
		  (let ((ima (environment-image env val))
			(head nil) )
		    (if (null ima)
			(push val sub1add)
			(if (term-is-variable? ima)
			    (push ima sub1add)
			    (if (and (term-is-application-form? ima)
				     (method-is-of-same-operator+ meth
								  (setq head
								    (term-method ima))))
				(setq sub1add
				      (nconc (reverse
					      (list-assoc-id-subterms ima head))
					     sub1add))
				(push ima sub1add)))))
		  (push val sub1add)))
 	    (setq sub1 (nreverse sub1add)) ; a bit tricky
	    ;; pdl - the following is invalid in AZ case, since a big term with
	    ;; ID's can shrink 
	    ;;	    (when (> (length sub1) (length sub2))
	    ;;	      (return-from no-match (values nil t)))
	    (multiple-value-setq (sub1 sub2)
	      (match-associative-id-simplify sub1 sub2))
	    ;; this never matches
	    (when (and (null sub1) sub2)
	      (return-from no-match (values nil t)))
	    ;;31 Mar 88 sub1 may be nil but have modified match-AZ-$..set-eq-state
	    (setf (%svref assoc-sys i)
	      (match-associativity-id-set-eq-state sub1 sub2))))
	(incf i))
      ;;
      (setq az-state (create-match-AZ-state dim meth assoc-sys))
      (when *match-debug*
	(format t "~%** AZ: initial state")
	(match-az-state-unparse az-state))
      (values az-state nil))))

;;; NEXT AZ State

(defun match-AZ-next-state (AZ-st)
  (declare (type match-az-state az-st))
  (let ((sys nil)
	(state nil)
	(no-more (match-az-state-no-more az-st))
	(zero nil))
    (if no-more
	(let ((zeros (pop (match-az-state-zero-matches az-st))))
	  (if zeros
	      (values zeros az-st nil)
	    (values nil nil t)))
      (progn
	(loop
	  (multiple-value-setq (sys state no-more zero)
	    (match-az-next-state-aux az-st))
	  ;; skip zero
	  (when no-more (return))
	  (when (not zero) (return))
	  (push sys (match-az-state-zero-matches az-st)))
	(if no-more
	    (match-az-next-state az-st)
	  (values sys state nil))))))

(defun match-az-next-state-aux (az-st)
  (let* ((new-sys (new-m-system))
 	 (sz (match-AZ-state-size AZ-st))
	 (sys (match-AZ-state-sys AZ-st))
	 (method (match-AZ-state-method AZ-st))
	 (made-zero nil))
    (declare (type list new-sys)
	     (type fixnum sz)
	     (type method method))
    (when (match-AZ-state-no-more AZ-st)	
      ;; there is no more match-AZ-state
      (return-from match-az-next-state-aux (values nil nil t nil)))
    ;;
    (dotimes-fixnum (k sz)		; k = 0,...,sz-1
      ;; i.e. for each equation of the system
      (let* ((eq-comp (%svref sys k))
	     (sz-left (match-equation-comp-sz-left eq-comp))
	     (left (match-equation-comp-left eq-comp))
	     (right (match-equation-comp-right eq-comp))
	     (sz-right (length (the simple-vector right)))
	     (comp (match-equation-comp-comp eq-comp)))
	(declare (type #-GCL simple-vector #+GCL vector comp))
	(dotimes-fixnum (l sz-left)	; l = 0,...,sz-left - 1
	  ;; i.e. for each term of the left hand 
	  ;; side of the equation 
   	  (let ((deb (if (= l 0)
			 0 
		       (%svref comp (1- l))))
		(fin (if (= l (1- sz-left)) 
			 sz-right
		       (%svref comp l)
		       ;; (1- (%svref comp l))
		       )))
	    (declare (type fixnum deb fin))
	    (multiple-value-bind (term zero?)
		(match-AZ-make-term method right deb fin)
	      (when zero? (setq made-zero t))
	      (add-equation-to-m-system new-sys (make-equation (%svref left l)
							       term)))))))
    (increment-the-match-AZ-state AZ-st) 
    (when *match-debug*
      (format t "~%** AZ: next state")
      (match-AZ-state-unparse AZ-st))
    (values new-sys AZ-st nil made-zero)))

;;; AZ EQUALITY

(defun match-AZ-equal (term1 term2)
  (declare (type term term1 term2))
  ;; strip zeros
  ;; (break)
  #||
  (princ "az:term1 = ")(term-print term1)
  (terpri)
  (princ "az:term2 = ")(term-print term2)
  (when (variables-occur-at-top? term1)
    (return-from match-az-equal nil))
  ||#
  ;;
  (if (term-is-applform? term2)
      (let ((head1 (term-head term1))
	    (head2 (term-head term2)))
	(if (method-is-of-same-operator head1 head2)
	    (let ((sub1 (list-assoc-id-subterms term1 head1))
		  (sub2 (list-assoc-id-subterms term2 head2)))
	      (declare (type list sub1 sub2))
	      (when (= (the fixnum (length sub1)) (the fixnum (length sub2)))
		(loop (unless sub1 (return-from match-az-equal t))
		    (unless (term-equational-equal (car sub1) (car sub2))
		      (return-from match-az-equal nil))
		  (setq sub1 (cdr sub1)
			sub2 (cdr sub2)))))
	    nil))
      nil))

(defun match-AZ-state-unparse (AZ-st)
  (format t "~&--AZ-state~%")
  (princ "size: ")(prin1 (match-AZ-state-size AZ-st))(terpri)
  (princ "operator: ")(prin1 (match-AZ-state-method AZ-st))(terpri)
  (princ "sys: ")(dotimes (x (length (the simple-vector
				       (match-AZ-state-sys AZ-st))))
		  (match-equation-comp-unparse (%svref (match-AZ-state-sys AZ-st) x))
		  )(terpri)
  (princ "no-more: ")(prin1 (match-AZ-state-no-more AZ-st))(terpri)
  )

(defun match-equation-comp-unparse (eq-comp)
  (princ "---unparse of: ")(prin1 eq-comp)(terpri)(terpri)
  (princ "---sz-left: ")(prin1 (match-equation-comp-sz-left eq-comp))(terpri)
  (princ "---left: ") (dotimes (x (length
				   (the simple-vector
				     (match-equation-comp-left eq-comp))))
			(prin1 (%svref (match-equation-comp-left eq-comp) x))
			)(terpri)
  (princ "---right; ") (dotimes (x (length
				    (the simple-vector
				      (match-equation-comp-right eq-comp))))
			 (prin1 (%svref (match-equation-comp-right eq-comp) x))
			 )(terpri)
  (princ "---comp")(prin1 (match-equation-comp-comp eq-comp))(terpri)
  )

;;; EOF
