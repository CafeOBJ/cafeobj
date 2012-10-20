;;;-*- Mode: Lisp; Syntax: CommonLisp Package: CHAOS -*-
;;; $Id: match-a.lisp,v 1.2 2007-04-03 06:46:14 sawada Exp $
(in-package :chaos)
#|==============================================================================
				  System:Chaos
				 Module:e-match
			       File:match-a.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; PROCEDURES for Associative Matching:========================================

;;; BASED ON matcher of OBJ3 Interpreter of SRI International:
;;; Copyright 1988,1991 SRI International.  All right reserved.

;;; A-STATE 
;;;   size   : the number of equations of the system.
;;;   method : the top operator(method) of each of the equations.
;;;            "f" for example, if f is associative and all the equations are 
;;;            of the form f(t1,...,tn) == f(...)
;;;   sys    : the system itself, presented as an array looking like:
;;;                t00 ,...,t0n == t'00,...,t'0p  x00,...,x0n-1
;;;                ...
;;;                ti0 ,...,tin == t'i0,...,t'ip  xi0,...,xin-1
;;;                ...
;;;            where a potential solution is deduced from the xi in the 
;;;            following way:
;;;            xi0 = f(t'i0,...,t'ixi0)
;;;            xij = f(t'_{i_{x_{i_{j-1}}+1}},....,t'_{i_{x_{i_{j}}}})
;;;            xin = f(t'_{i_{x_{i_{n-1}}+1}},....,t'_{i_n})
;;;
;;;(defstruct (match-A-state
;;;             (:type vector)
;;;             (:conc-name match-a-state-void)
;;;             (:constructor make-match-A-state (size method sys no-more)))
;;;  (size 0 :type fixnum :read-only t)    ; number of equations of the system.
;;;  (method nil :read-only t)             ; top operator.
;;;  sys                                   ; array[eq-comp].
;;;  (no-more nil)                         ; bool, a flag indicating no more possible state.
;;;  )

(deftype match-a-state () 'list)

(defmacro make-match-a-state (size!*_? method!*_? sys!*_?)
  `(list ,size!*_? ,method!*_? ,sys!*_? nil))

(defmacro match-a-state-size (as----_)  `(the fixnum (car ,as----_)))
(defmacro match-a-state-method (as----_)  `(cadr ,as----_))
(defmacro match-a-state-sys (as----_)  `(caddr ,as----_))
(defmacro match-a-state-no-more (as----_)  `(cadddr ,as----_))
    
;;;(defstruct (match-equation-comp
;;;             (:type vector)
;;;             (:conc-name match-equation-comp-void)
;;;             (:constructor make-match-equation-comp (sz-left left right comp)))
;;;  (sz-left 0 :type fixnum :read-only t)
;;;  left
;;;  right
;;;  comp
;;;  )
(deftype match-equation-comp () 'list)
(defmacro make-match-equation-comp (*_*_sz-left *_*_left *_*_right *_*_comp)
  `(list ,*_*_sz-left ,*_*_left ,*_*_right ,*_*_comp))

(defmacro match-equation-comp-sz-left (???_v)
  `(the fixnum (car ,???_v)))
(defmacro match-equation-comp-left (?v__?)
  `(the #-GCL simple-vector #+GCL vector (cadr ,?v__?)))
(defmacro match-equation-comp-right (?+_v)
  `(the #-GCL simple-vector #+GCL vector (caddr ,?+_v)))
(defmacro match-equation-comp-comp (v__?)
  `(the #-GCL simple-vector #+GCL vector (cadddr ,v__?)))
  
(defun print-equation-comp (e-c)
  (princ "[equation-comp size left: ") (prin1 (match-equation-comp-sz-left e-c))
  (print-next)
  (princ "left:")
  (print-term-seq (match-equation-comp-left e-c))
  (print-next)
  (princ "right:")
  (print-term-seq (match-equation-comp-right e-c))
  (print-next)
  (princ " comp: ") (prin1 (match-equation-comp-comp e-c))
  (princ "]")
  )

;;; Simplify the left symbols and the right symbols. Returns the modified list
;;; of terms.  
;;; EXAMPLE: (a,x,c,z,d,c) == (a,b,b,b,c,c,c,c) is simplified into
;;;            (x,c,z,d)   ==   (b,b,b,c,c,c)
;;; NOTICE that a variable  appearing in the right hand side
;;; should never be simplified. It  will be the case
;;; if the right hand side is always renamed before matching ...
;;;
(declaim (inline match-associative-simplify))

(#-GCL defun #+GCL si:define-inline-function
       match-associative-simplify (sub1 sub2)
  (declare (type list sub1 sub2)
	   (values (or null t)))
  ;;
  (do ((t1 (car sub1) (car sub1))
       (t2 (car sub2) (car sub2)))
      ((or (null sub1)
	   (null sub2)
	   (term-is-variable? t1)
	   (not (term-equational-equal t1 t2))))
    (declare (type term t1 t2))
    (pop sub1)
    (pop sub2))
  ;;
  (setq sub1 (nreverse sub1)
	sub2 (nreverse sub2))
  (do ((t1 (car sub1) (car sub1))
       (t2 (car sub2) (car sub2)))
      ((or (null sub1)
	   (null sub2)
	   (term-is-variable? t1)
	   (not (term-equational-equal t1 t2))))
    (declare (type term t1 t2))
    (pop sub1)
    (pop sub2))
  ;;
  (let ((numvars 0))
    (declare (type fixnum numvars))
    (dolist (x1 sub1)
      (declare (type term x1))
      (when (term-is-variable? x1) (incf numvars)))
    (if (and (<= 2 numvars)
	     (<= 3 (the fixnum (length sub1)))
	     (<= 5 (the fixnum (length sub2))))
	(if (block test1
	      (dolist (x1 sub1 nil)
		(declare (type term x1))
		(unless (term-is-variable? x1)
		  (dolist (x2 sub2 (return-from test1 t))
		    (declare (type term x2))
		    (when (and (not (term-is-variable? x2))
			       (possibly-matches-nonvar x1 x2))
		      (return))))))
	    (values nil nil t)
	    (values (nreverse sub1) (nreverse sub2) nil))
	(values (nreverse sub1) (nreverse sub2) nil))))

(declaim (inline match-associativity-set-eq-state))
	 
(#-GCL defun #+GCL si:define-inline-function
       match-associativity-set-eq-state (sub1 sub2)
  (declare (type list sub1 sub2))
  (let* ((sz1 (length sub1))
	 (comp (alloc-svec-fixnum (if (= 0 sz1) 0 (- sz1 1)))))
    (declare (type #+GCL vector #-GCL simple-vector comp)
	     (type fixnum sz1))
    (dotimes (x (- sz1 1))
      (declare (type fixnum x))
      ;; x = 0,...,sz1-2
      ;;built the array (1, 2, 3, 4) if sz1 = 5 
      (setf (svref comp x) (1+ x)))
    (make-match-equation-comp sz1
			      (apply #'vector sub1)
			      (apply #'vector sub2)
			      comp)))

;;; Create a single term from a collection of terms
;;;
(declaim (inline match-a-make-term))

(#-GCL defun #+GCL si:define-inline-function
       match-A-make-term (method vect first last)
  (declare (type fixnum first last)
	   (type #+GCL vector #-GCL simple-vector vect))
  (if (= first last)
      (svref vect first)
      (let ((res (svref vect last)))
	(if (and (< 1 (the fixnum (- last first)))
		 (null (cdr (method-lower-methods method))))
	    (do ((i (1- last) (1- i)))
		((< i first) res)
	      (declare (type fixnum i))
	      #||
	      (setq res (make-applform (method-coarity method)
				       method (list (svref vect i) res)))
	      ||#
	      (setq res (make-term-with-sort-check method
						   (list (svref vect i) res)))
	      )
	  (do ((i (1- last) (1- i)))
	      ((< i first) res)
	    (declare (type fixnum i))
	    (setq res (make-term-with-sort-check-bin method 
						     (list (svref vect i) res)))
	    )))))

;;; Returns the list of terms contained in the array of terms "t-arr"
;;; between the indices "from" and "to" both included.
;;; Example: match-A-extract-in-from-to((1,2,3,4,5,6), 1, 4) --> (2,3,4,5)
;;; note that the indices of the array are 0,1,2,3,4,5.
;;;
(declaim (inline match-a-extract-in-from-to))

(#-GCL defun #+GCL si:define-inline-function
       match-A-extract-in-from-to (t-arr from to)
  (declare (type fixnum from to)
	   (type #+GCL vector #-GCL simple-vector t-arr))
  (let ((t-list nil))
    (do ((i to (1- i)))
	((< i from)  t-list)
      (declare (type fixnum i))
      (push (svref t-arr i) t-list))))

;;; Modify the match-A-state "A-st" by  incrementing the state local to each
;;; equation of the system in a "variable basis numeration" way
;;;
(declaim (inline increment-the-match-a-state))

(#-GCL defun #+GCL si:define-inline-function
       increment-the-match-A-state (A-st)
  (block the-end
    (let ((sz (match-A-state-size A-st))
	  (sys (match-A-state-sys A-st)))
      (declare (type fixnum sz)
	       (type #+GCL vector #-GCL simple-vector sys))
      (let ((k 0)
	    eq-comp)
	(declare (type fixnum k))
	(while (> sz k)
	  (setq eq-comp (svref sys k))
	  (when (match-A-try-increase-lexico
		 (match-equation-comp-comp eq-comp)
		 (1- (the fixnum
		       (length (match-equation-comp-right eq-comp)))))
	    ;; note that match-A-try-increase-lexico modify in this case
	    ;; the  "comp"  of the current equation.
	    ;; After that the previous composant are reset like in
	    ;; 599 -> 600
	    (match-A-reset-match-equation-comp sys k)
	    (return-from the-end (values nil)))
	  ;;otherwise, try to increase the next equation
	  (setq k (1+ k))
	  ))
      ;; this "normal" exit of the loop means that none of the
      ;; state has been increased so there is no more state
      (setf (match-A-state-no-more A-st) t)
      )))

;;; Try to increase with respect with the lexicographical order
;;; on the arrays of integer the integer array "comp". These are
;;; the following constaints:
;;; 1) the elements of the array are all different and ordered in 
;;; increasing order: example (2 3 4 6 8)
;;; 2) the grastest element of the array in LESS OR EQUAL to "max"
;;; Returns true iff one have succeded to increment.
;;;
(declaim (inline match-a-try-increase-lexico))

(#-GCL defun #+GCL si:define-inline-function
       match-A-try-increase-lexico (comp max)
  (declare (type fixnum max)
	   (type #+GCL vector #-GCL simple-vector comp))
  (let ((lim (1- (length comp))))
    (declare (type fixnum lim))
    (do ((i lim (- i 1)))
	((< i 0) nil)
      (declare (type fixnum i))
      (let ((x (svref comp i)))
	(declare (type fixnum x))
	(when (< x max)
	  (setf (svref comp i) (1+ x))
	  (do ((j (1+ i) (1+ j))
	       (v (+ x 2) (1+ v)))
	      ((< lim j))
	    (declare (type fixnum j v))
	    (setf (svref comp j) v))
	  (return t)))
      (setq max (1- max)))))

;;; Reset the comp of "eq-comp" to his initial value i.e. (1,2,3,4,5)
;;;
(declaim (inline match-a-reset-comp))

(#-GCL defun #+GCL si:define-inline-function
       match-A-reset-comp (eq-comp)
  (let ((comp (match-equation-comp-comp eq-comp)))
    (declare (type #+GCL vector #-GCL simple-vector comp))
    (dotimes (x (1- (match-equation-comp-sz-left eq-comp)))
      (declare (type fixnum x))
      (setf (aref comp x) (1+ x)))))

;;; Modifies the array "sys" of "match-equation-comp" in such a way that
;;; all the comp array are reset provide that they rank in "sys"
;;; is less (strictly) than K.
;;;
(declaim (inline match-a-reset-match-equation-comp))

(#-GCL defun #+GCL si:define-inline-function
       match-A-reset-match-equation-comp (sys K)
  (declare (type #+GCL vector #-GCL simple-vector sys)
	   (type fixnum k))
  (dotimes (i K)				; i = 0,...,K-1 
    (declare (type fixnum i))
    (match-A-reset-comp (svref sys i))))


;;; A-STATE Initialization -----------------------------------------------------

;;; Initialize an associative state. Suppose that for any equation t1 == t2 of
;;; "sys", t1 and t2 are not E-equal. 
;;;
;;; 0) take the associative normal form (at the first level) of each term of the
;;;    system.
;;; 1) checks if the top symbols of each equation of the system have the same
;;;    (associative) head function. 
;;; 2) checks if length(Left[i]) =< length(Right[i])
;;; 3) simplifies all the similar term in Left[i] and Right[i]  at their left
;;;    or right extremity.
;;; 4) initialize left-state.
;;;
(defun match-A-state-initialize (sys env)
  (block no-match
    (let* ((dim nil)
	   (assoc-sys nil)
	   (method nil)
	   (i 0))
      (declare (type fixnum i)
	       (type (or null fixnum) dim)
	       (type #+GCL (or null vector)
		     #-GCL (or null simple-vector)
		     assoc-sys)
	       )
      (dolist (equation (m-system-to-list sys))
	(let ((t1 (equation-t1 equation))
	      (t2 (equation-t2 equation)))
	  (unless (and (term-is-application-form? t2)
		       (method-is-of-same-operator+ (term-method t1)
						    (term-method t2))
		       (setq method (term-method t1)))
	    (return-from no-match (values nil t)))
	  ;;
	  (let* ((sub1 (list-assoc-subterms t1 method))
		 (sub1add nil)
		 (sub2 (list-assoc-subterms t2 method))
		 (sub2-len (length sub2))
		 (fail nil))
	    (declare (type list sub1 sub2)
		     (type fixnum sub2-len))
	    ;;
	    ;;(when (> (the fixnum (length sub1)) sub2-len)
	    ;;  (return-from no-match (values nil t)))
	    ;;
	    ;; add the additional information contained in "env" into "sub1".
	    (dolist (val sub1)
	      (declare (type term val))
	      (if (term-is-variable? val)
		  (let ((image (environment-image env val))
			(head nil))
		    (declare (type (or null term) image))
		    (if (null image)
			(push val sub1add)
			(if (term-is-variable? image)
			    (push image sub1add)
			  (if (eq method (setf head (term-method image)))
			      (setq sub1add
			        (nconc
			         (reverse
			          (list-assoc-subterms image head))
			         sub1add))
			    (push image sub1add)))))
		(push val sub1add)))
	    ;;
	    (setq sub1 (nreverse sub1add))
	    ;;
	    (when (> (the fixnum (length sub1)) sub2-len)
	      (return-from no-match (values nil t)))
	    (multiple-value-setq (sub1 sub2 fail)
		(match-associative-simplify sub1 sub2))
	    (when (or fail
		      (and (null sub1) sub2)
		      (and (null sub2) sub1))
	      (return-from no-match (values nil t)))
	    ;; sub1 may be nil but have modified match-A-..set-eq-state
	    (unless assoc-sys
	      (setq dim (size-of-m-system sys))
	      (setq assoc-sys (alloc-svec (the fixnum dim))))
	    (setf (svref assoc-sys i)
		  (match-associativity-set-eq-state sub1 sub2))))
	(setq i (1+ i)))
      (values (make-match-A-state dim method assoc-sys)
	      nil))))

;;; ASSOCITIVITY NEXT STATE ----------------------------------------------------

(defun match-A-next-state (A-st)
  (declare (type match-a-state a-st)
	   (values list (or null match-a-state) (or null t)))
  (let* ((new-sys (new-m-system))
 	 (sz (match-A-state-size A-st))
	 (sys (match-A-state-sys A-st))
	 (method (match-A-state-method A-st)))
    (declare (type fixnum sz)
	     (type vector sys))
    (if (match-A-state-no-more A-st)	
	;; there is no more match-A-state.
	(values nil nil t)
        (progn
	  (dotimes (k sz)
	    (declare (type fixnum k))
	    ;; for each equation of the system
	    (let* ((eq-comp (svref sys k))
		   (sz-left (match-equation-comp-sz-left eq-comp))
		   (left (match-equation-comp-left eq-comp))
		   (right (match-equation-comp-right eq-comp))
		   (sz-right (1- (the fixnum (length right))))
		   (comp (match-equation-comp-comp eq-comp)))
	      (declare (type fixnum sz-left sz-right)
		       (type #+GCL vector #-GCL simple-vector left right)
		       (type #+GCL vector #-GCL simple-vector comp))
	      (dotimes (l sz-left)
		(declare (type fixnum l))
		;; i.e. for each term of the left hand 
		;; side of the equation 
		(let ((deb (if (= l 0)
			       0 
			       (svref comp (the fixnum (1- l)))))
		      (fin (if (= l (the fixnum (1- sz-left)))
			       sz-right 
			       (1- (the fixnum (svref comp l))))))
		  (declare (type fixnum deb fin))
		  (add-equation-to-m-system
		   new-sys
		   (make-equation
		    (svref left l)
		    (match-A-make-term method right deb fin)))))
	      ))
	  (increment-the-match-A-state A-st) ; A-st is modified
	  (values new-sys A-st nil)))))


;;; Associative Equational Equal ------------------------------------------------ 

;;; match-A-equal: Term Term -> Bool
;;;
(defun match-A-equal (t1 t2)
  (declare (type term t1 t2)
	   (values (or null t)))
  (if (term-is-application-form? t2)
      (let ((hd2 (term-method t2)))
	(if (method-is-of-same-operator (term-head t1)
					hd2)
	    (let ((l1 (list-assoc-subterms t1 (term-method t1)))
		  (l2 (list-assoc-subterms t2 hd2)))
	      (declare (type list l1 l2))
	      (and (= (the fixnum (length l1)) (the fixnum (length l2)))
		   (loop (when (null l1) (return (null l2)))
		       (unless (term-equational-equal (car l1) (car l2))
			 (return nil))
		     (setq l1 (cdr l1) l2 (cdr l2)))))
	    nil))
      nil))
 
;;; EOF
