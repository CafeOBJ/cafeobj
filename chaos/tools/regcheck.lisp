;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
				 System: Chaos
			         Module: tools
			       File: recheck.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; (defvar *regularize-debug* nil)

;;; ***
;;; SOP_________________________________________________________________________
;;; ***
;;; SOP gathers methods of an operator. Methods are categorized into two
;;; groups: empties and non-empties, which are a set of empty methods
;;; (i.e., methods with some argument sorts are empty sorts) and non-empty
;;; methods respectively.
;;;
(defstruct (sop (:type list)(:copier nil)
		(:constructor create-sop (operator)))
  (operator nil)			; operator.
  (empties nil)				; set of methods whose arity contains
					; some empty sort.
  (non-empties nil)			; non-empty methods.
  )

(defun print-sop (sop &optional (module (or *current-module*
					    *last-module*)))
  (with-in-module (module)
    (format t "~%** SOP : operator ")
    (print-chaos-object (sop-operator sop))
    (format t "~%-- empty methods")
    (if (sop-empties sop)
	(let ((*print-indent* (+ 2 *print-indent*)))
	  (dolist (meth (sop-empties sop))
	    (print-next)
	    (print-chaos-object meth)))
	(princ " : None"))
    (format t "~%-- non empty methods")
    (if (sop-non-empties sop)
	(let ((*print-indent* (+ 2 *print-indent*)))
	  (dolist (meth (sop-non-empties sop))
	    (print-next)
	    (print-chaos-object meth)))
	(princ " : None"))))

;;; ***********
;;; SORT MARK  __________________________________________________________________
;;; ***********
;;; sorts are marked iff it is non-empty, i.e., has at least one term of the sort. 
;;; 
(defun is-sort-marked? (s)
  (sort-is-inhabited s))

(defun mark-sort (s &optional (so *current-sort-order*))
  (setf (sort-is-inhabited s) t)
  (dolist (x (supersorts-no-err s so))
    (setf (sort-is-inhabited x) t)))

(defun unmark-sorts (sl)
  (dolist (s sl) (setf (sort-is-inhabited s) nil)))

(defmacro get-unmarked-sorts ($_?sl)	; not used?
  ` (let (($$res_ nil))
      (dolist (*_s ,$_?sl)
	(unless (sort-is-inhabited *_s)
	  (push *_s $$res_)))
      $$res_))

;;; -----------------------
;;; CHECK-SIGNATURE-EMPTIES
;;;   : Module -> List[empty-sort] List[non-empty-sort] List[Sop]
;;;
(defun check-signature-empties (module)
  (let ((esorts nil)
	(nesorts nil)
	(neops nil))
    (clear-tmp-sort-cache)
    (with-in-module (module)
      (let ((sorts (module-all-sorts module))
	    (sops nil))
	;; initially, all sorts are marked empty.
	(unmark-sorts sorts)
	;; mark builtin sorts as non-empty
	(dolist (x sorts)
	  (when (or (eq (sort-module x) *chaos-module*)
		    (sort-is-builtin x)
		    (and-sort-p x))
	    (mark-sort x)
	    (pushnew x nesorts :test #'eq)))
	;; and all operators are assumed to be empty.
	;; note we ignore error operators
	(dolist (opinfo (module-all-operators module))
	  (let* ((methods (opinfo-methods opinfo))
		 (op-name (operator-name (opinfo-operator opinfo)))
		 (sop (find-if #'(lambda (x)
				   (equal op-name
					  (operator-name (sop-operator x))))
			       sops)))
	    (unless sop
	      (setq sop (create-sop (opinfo-operator opinfo)))
	      (push sop sops))
	    ;;
	    (dolist (method methods)
	      (unless (method-is-error-method method)
		(push method (sop-empties sop))
		))))
	
	;; iterate while there are no changes in empty sorts,
	;; or empty methods.
	(let ((changed? t))
	  (while changed?
	    (setq changed? nil)
	    ;;
	    (dolist (sop sops)
	      (let ((eop nil))
		(dolist (method (sop-empties sop))
		  (if (every #'(lambda (x) (is-sort-marked? x))
			     (method-arity method))
		      (progn
			(setq changed? t)
			(push method (sop-non-empties sop))
			(push method neops)
			(dolist (s (super-or-equal-sorts (method-coarity method)))
			  (mark-sort s)
			  (pushnew s nesorts :test #'eq)))
		      (progn
			(push method eop))))
		(setf (sop-empties sop) eop)))))

	;; check is done.
	;;
	(setq esorts
	      (set-difference sorts
			      nesorts :test #'eq))
	(values esorts nesorts sops neops)))))

;;;
;;;
;;;
(defvar *regularize-glb-sorts-so-far* nil)
(defvar *regularize-sorts-to-be-added* nil)
(defvar *regularize-methods-so-far* nil)
(defvar *regularize-methods-to-be-added* nil)
;;;
;;; REGULARIZE-MAKE-GLB
;;;
(defvar *regularize-optimize* t)

(defun regularize-make-glb (sorts module)
  (let ((so (module-sort-order module)))
    (setq sorts (minimal-sorts sorts so))
    (unless (cdr sorts)
      (return-from regularize-make-glb (values (car sorts) nil)))
    ;;
    (let ((xset (mapcar #'(lambda (x)
			    (reg-direct-sub-or-equal-sorts x so))
			sorts)))
      (let ((glb nil)
	    (meets (car xset)))
	(dolist (xs (cdr xset))
	  (setq meets (intersection meets xs)))
	(if meets
	    (setq meets (maximal-sorts meets so))
	    (setq meets (minimal-sorts sorts so)))
	;;
	(unless (cdr meets)
	  (when (and-sort-p (car meets))
	    (return-from regularize-make-glb (values (car meets) nil))))
	;;
	(when *regularize-debug*
	  (format t "~&** making glb from sorts :")
	  (print-chaos-object sorts))
	
	(setq glb (make-glb-sort sorts module))
	;;
	;; further optimization can be done here, but...
	;;
	(let ((pre (find-if #'(lambda (x)
				(when *regularize-optimize*
				  (reg-sort-included x glb so)
				  (equal (sort-id glb)
					 (sort-id x)))
				)
			    *regularize-glb-sorts-so-far*)))
	  (when pre
	    (return-from regularize-make-glb (values pre nil)))
	  (push glb *regularize-glb-sorts-so-far*)
	  (values glb t))))))

(defun reg-direct-subsorts (sort sort-order)
  (cond ((and-sort-p sort)
	 (let ((subs nil))
	   (dolist (x (and-sort-components sort))
	     (dolist (s (reg-direct-subsorts x sort-order))
	    (pushnew s subs :test #'eq)))
	   subs))
	(t (direct-subsorts sort sort-order))))

(defun reg-sub-or-equal-sorts (sort sort-order)
  (cons sort (reg-direct-subsorts sort sort-order)))

(defun reg-direct-sub-or-equal-sorts (sort sort-order)
  (if (and-sort-p sort)
      (let ((subs nil))
	(dolist (x (and-sort-components sort))
	  (dolist (s (reg-direct-sub-or-equal-sorts x sort-order))
	    (pushnew s subs :test #'eq)))
	(pushnew sort subs :test #'eq))
      (cons sort (direct-subsorts sort sort-order))))

(defun reg-sort<= (s1 s2 so)
  (cond ((and-sort-p s1)
	 (some #'(lambda (x)
		   (reg-sort<= x s2 so))
	       (and-sort-components s1)))
	((and-sort-p s2)
	 (every #'(lambda (x)
		    (reg-sort<= s1 x so))
		(and-sort-components s2)))
	(t (if (sort<= s1 s2 so)
	       t
	       nil)))
  )

;;; assume that both s1 and s2 are and-sorts.
;;;  s1 <= s2
(defun reg-sort-included (s1 s2 so)
  (declare (ignore so))
  (unless (and (and-sort-p s1) (and-sort-p s2))
    (with-output-panic-message ()
      (format t "[reg-sort-included]: assumption failure!")
      (print-next)(princ "s1 = ")(print-chaos-object s1)
      (print-next)(princ "s2 = ")(print-chaos-object s2)
      (chaos-error 'panic)))
  (let ((compo1 (and-sort-components s1))
	(compo2 (and-sort-components s2)))
    (every #'(lambda (x)
	       (memq x compo2))
	   compo1)))

(defun reg-sort-list<= (sl1 sl2 so)
  (declare (type list sl1 sl2)
	   (type sort-order so))
  (and (= (the fixnum (length sl1)) (the fixnum (length sl2)))
       (every #'(lambda (x y) (reg-sort<= x y so)) sl1 sl2)))

(defun reg-sort< (s1 s2 so)
  (cond ((and-sort-p s1)
	   (some #'(lambda (x)
		     (reg-sort< x s2 so))
		 (and-sort-components s1)))
	((and-sort-p s2)
	 (every #'(lambda (x)
		    (reg-sort< s1 x so))
		(and-sort-components s2)))
	(t (if (sort< s1 s2 so)
	       t
	       nil)))
  )

(defun reg-sort-list= (sl1 sl2)
  (equal sl1 sl2))
  
;;; EXAMINE-REGULARITY module
;;; checks if the signature of given module is regular or not.
;;;
(defun examine-regularity (module)
  (multiple-value-bind (empty-sorts
			non-empty-sorts
			sops
			non-empties)
      (check-signature-empties module)
    (declare (ignore non-empty-sorts))
    ;;
    (setq *regularize-glb-sorts-so-far* (module-sorts-for-regularity module)
	  *regularize-sorts-to-be-added* nil
	  *regularize-methods-so-far* nil
	  *regularize-methods-to-be-added* nil)
    ;;
    (with-in-module (module)
      (let ((new-sorts nil)
	    (new-methods nil)
	    (redundant-methods nil)
	    (empty-methods nil))
	;; step-1
	;; make new and-sorts which are necessary for regularity.
	;; for each connected component of sorts, we possibly need
	;; a new and-sort.
	;; and for each combination of sort ilands, we also need possibly
	;; a new and-sort.
	;; we make each from non-empty methods.
	(when *chaos-verbose*
	  (format t "~&(checking sorts for regularity:"))
	(dolist (opinfo (module-all-operators module))
	  (block make-coarity
	    ;; step 1.1 : first we make glb sort for connected components.
	    (let ((entry (find-if #'(lambda (x)
				      (equal (car x)
					     (operator-name
					      (opinfo-operator opinfo))))
				  new-sorts)))
	      (unless entry
		(setq entry (cons (operator-name (opinfo-operator opinfo))
				  nil))
		(push entry new-sorts))
	      ;; optimization here? eliminate builtin ops...
	      (let ((methods (remove-if #'(lambda (x)
					    (method-is-error-method x))
					(opinfo-methods opinfo))))
		(let ((new-coarity nil)
		      (coarities nil))
		  (dolist (meth methods)
		    (when (memq meth non-empties)
		      (pushnew (method-coarity meth) coarities :test #'eq)))
		  (unless coarities
		    (return-from make-coarity nil))
		  
		  ;; compute new coarity
		  (multiple-value-bind (ncor new?)
		      (regularize-make-glb coarities module)
		    (declare (ignore new?))
		    (setq new-coarity ncor))
		  ;;
		  (pushnew new-coarity (cdr entry) :test #'eq)
		  (when (and-sort-p new-coarity)
		    (pushnew new-coarity *regularize-sorts-to-be-added*
			     :test #'eq))
		  )))
	    ))
	(when *chaos-verbose* (princ ")")(terpri)(force-output))
	;; step 1.2
	;; we make glb for each combinations of sort ilands.
	;; note: new-sorts is the form of List[(operator-name sorts)].
	#|| TOO MUCH, this is not needed.
	(dolist (cg new-sorts)
	  (let ((new nil))
	    (do ((ss (cdr cg) (cdr ss)))
		((endp ss))
	      (dolist (s (cdr ss))
		(multiple-value-bind (glb new?)
		    (regularize-make-glb (list (car ss) s) module)
		  (when new?
		    ;; note, because the disjointness, new? is the
		    ;; tigger to add.
		    (push glb *regularize-sorts-to-be-added*)
		    (mark-sort glb))
		  (pushnew glb new :test #'eq))))
	    (setf (cdr cg) (nconc (cdr cg) new))
	    ))
	||#
	;;
	(when *regularize-debug*
	  (format t "~%** step1 result :")
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (princ "- sorts for each operator symbol :")
	    (dolist (s new-sorts)
	      (print-next)
	      (print-chaos-object (car s))
	      (princ " : ")
	      (print-chaos-object (cdr s)))
	    (print-next)
	    (princ "- sorts to be added!")
	    (print-next)
	    (print-chaos-object *regularize-sorts-to-be-added*)))

	;;-----------------------------------------------------
	;; step-2
	;; now *regularize-sorts-to-be-added* is the sufficient
	;; set of and-sorts for regularity.
	;; based on these, we construct new methods if need.
	;; here, we consider each group of overloaded operators
	;; (including ad hoc overloading), sops returned from
	;; check-signature-empties organized so.
	;;

	(when (or *chaos-verbose* *regularize-debug*)
	  (princ "(start checking operators : "))
	(dolist (sop sops)
	  ;; step 2-1. first we construct ranks which may be
	  ;;           necessary for regularity.
	  ;;           the result will be hold in new-ranks.
	  (let ((methods (sop-non-empties sop))
		(name (operator-name (sop-operator sop)))
		(cent nil)
		(redun-methods nil)
		(new-ranks nil))
	    ;;
	    (when (or *chaos-verbose* *regularize-debug*)
	      (format t "~{~a~^ ~a~} " (car name)))
	    ;;
	    (setq cent (find-if #'(lambda (x)
				    (equal name (car x)))
				new-sorts))
	    (unless cent (return nil))	; no possibility 
	    ;;
	    ;; loop until no more pssible new rank ...
	    ;;
	    (let ((changed? t))
	      (while changed?
		(when (or *chaos-verbose* *regularize-debug*)
		  (princ ".")
		  (force-output))
		(setq changed? nil)
		(block make-new-rank
		  ;; for each combination.
		  (do ((mm methods (cdr mm)))
		      ((endp mm))
		    (dolist (m (cdr mm)) ; makes combination
		      (block make-rank
			(let ((new-ar (make-list
				       (the fixnum
					 (length (the list
						   (reg-method-arity m))))))
			      (new-cr nil)
			      (a1 (reg-method-arity (car mm)))
			      (a2 (reg-method-arity m))
			      (c1 (reg-method-coarity (car mm)))
			      (c2 (reg-method-coarity m)))
			  (declare (type list a1 a2)
				   (type sort* c1 c2))
			  ;;
			  (when *regularize-debug*
			    (let ((*print-indent* (+ 2 *print-indent*)))
			      (print-next)
			      (princ "- check comination of ")
			      (print-chaos-object (car mm))
			      (print-next)
			      (princ "  .vs. ")
			      (print-chaos-object m)))
			  ;;
			  (dotimes (x (length a1))
			    (declare (type fixnum x))
			    (multiple-value-bind (glb new?)
				(regularize-make-glb (list (nth x a1)
							   (nth x a2))
						     module)
			      (cond (new? (return-from make-rank nil))
				    ((and-sort-p glb)
				     (unless (memq glb
						   *regularize-sorts-to-be-added*)
				       (return-from make-rank nil))))
			      (setf (nth x new-ar) glb)))
			  ;; search for proper coarity.
			  (multiple-value-bind (glb new?)
			      (regularize-make-glb (list c1 c2)
						   module)
			    (when new?
			      (if (and-sort-p glb)
				  (not (every #'(lambda (x)
						  (is-sort-marked? x))
					      (and-sort-components glb)))
				  (return-from make-rank nil)))
			    (setq new-cr glb))
			  ;;
			  (unless new-cr 
			    (return-from make-rank nil))
			  ;; new-ar and new-cr contais possible new rank
			  ;; for this combination.
			  ;; we register it to new
			  (when *regularize-debug*
			    (let ((*print-indent* (+ *print-indent* 2)))
			      (print-next)
			      (princ "trying to add new rank ")
			      (print-chaos-object (list new-ar new-cr))))
			  ;;
			  ;; redundancy check
			  ;;
			  (multiple-value-bind (to-add? method-list redundant)
			      (check-method-redundancy new-ar new-cr methods module)
			    (setq redun-methods (nconc redun-methods redundant))
			    (when to-add?
			      (setq changed? t)
			      (when *regularize-debug*
				(princ " ... new one! added."))
			      (pushnew (list new-ar new-cr) new-ranks :test #'equal)
			      (mark-sort new-cr)
			      (pushnew new-cr *regularize-sorts-to-be-added*
				       :test #'eq)
			      ;; we try from new intial stage...
			      (setq methods method-list)
			      (return-from make-new-rank nil)))
			  ))		; block make-rank
		      ))		; end all possible combination of an op.
		  )			; block make-new-rank
		)			; end of while
	      )
	    ;; we end for each combination of this overloaded operators.
	    ;; new contains new raks.
	    (let ((*print-indent* (+ *print-indent* 2)))
	      (when new-ranks
		(push (cons (sop-operator sop)
			    new-ranks)
		      new-methods))
	      (setf redundant-methods
		    (nconc redundant-methods redun-methods))
	      ;;
	      (when *regularize-debug*
		(print-next)
		(princ "- new ranks :")
		(if new-ranks
		    (dolist (e new-ranks)
		      (print-next)
		      (print-chaos-object e))
		    (princ "None"))))
	    ;;
	    ))				; end of all operator groups.
	;;
	;; returns the whole result
	;;
	(when (or *chaos-verbose* *regularize-debug*)
	  (princ ")")
	  (terpri)
	  (force-output))
	(dolist (sop sops)
	  (setq empty-methods
		(nconc empty-methods (sop-empties sop))))
	(setq empty-methods
	      (delete-duplicates empty-methods :test #'equal))
	(setq redundant-methods
	      (delete-duplicates redundant-methods :test #'equal))
	(let ((ns nil))
	  #||
	  (dolist (x new-sorts)
	    (dolist (s (cdr x))
	      (when (and (and-sort-p s)
			 (is-sort-marked? s)
			 (not (memq s (module-sorts module))))
		(pushnew s ns :test #'eq))))
	  ||#
	  (dolist (s *regularize-sorts-to-be-added*)
	    (when (and (and-sort-p s)
		       (is-sort-marked? s)
		       (not (memq s (module-sorts module))))
	      (pushnew s ns :test #'eq)))
	  ;;
	  (values empty-sorts
		  ns
		  new-methods
		  redundant-methods
		  empty-methods))
	))))

(defun reg-report-method (m module)
  (cond ((operator-method-p m)
	 (print-chaos-object m))
	(t (let ((name (operator-symbol (car m)))
		 (ranks (cdr m))
		 (f nil))
	     (dolist (rank ranks)
	       (when f (print-next))
	       (setq f t)
	       (format t "~{~a~} : " name)
	       (dolist (s (car rank))
		 (print-sort-name s module)
		 (princ " "))
	       (princ "-> ")
	       (print-sort-name (cadr rank) module)
	       )))))

(defun reg-method-arity (m)
  (if (operator-method-p m)
      (method-arity m)
      (car m)))

(defun reg-method-coarity (m)
  (if (operator-method-p m)
      (method-coarity m)
      (cadr m)))

(defun check-method-redundancy (arity coarity method-list
				      &optional (module (or *current-module*
							    *last-module*)))
  (let ((so (module-sort-order module))
	(redundant-methods nil)
	(not-tobe-added? nil))
    (let ((new-set nil))
      (dolist (meth method-list)
	(cond ((reg-sort-list= arity (reg-method-arity meth))
	       (when *regularize-debug*
		 (let ((*print-indent* (+ *print-indent* 2)))
		   (format t "~%- check redundancy with :")
		   (print-chaos-object meth)))
	       ;;
	       (when (sort= (reg-method-coarity meth) coarity)
		 (when *regularize-debug*
		   (format t "~%- there already the same one."))
		 (return-from check-method-redundancy
		   (values nil method-list nil)))
	       ;;
	       (if (cond ((and-sort-p coarity)
			  (reg-sort<= coarity (reg-method-coarity meth) so))
			 (t (reg-sort< coarity (reg-method-coarity meth) so)))
		   (progn
		     (when *regularize-debug*
		       (format t "~%- redundant.."))
		     (push meth redundant-methods))
		   (progn
		     (when *regularize-debug*
		       (format t "~%- not redundant.."))
		     (push meth new-set))))
	      (t (push meth new-set))))
      ;;
      (setq method-list new-set)
      (unless (setq not-tobe-added?
		    (dolist (d new-set nil)
		      (when (and (reg-sort-list= (reg-method-arity d) arity)
				 (reg-sort< (reg-method-coarity d) coarity so))
			(return t))))
	(push (list arity coarity) method-list))
      ;;
      (values (not not-tobe-added?) method-list redundant-methods)
      ;;
      )))

;;;
;;; CHECK-REGULARITY : Module -> ...
;;;
(defun check-regularity (module &optional (silent nil))
  (multiple-value-bind (empty-sorts
			new-sorts
			new-methods
			redundant-methods
			empty-methods)
      (examine-regularity module)
    ;;
    (unless (or empty-sorts new-sorts new-methods redundant-methods empty-methods)
      (unless silent
	(with-output-msg ()
	  (princ "signature of module ")
	  (print-chaos-object module)
	  (princ " is regular.")))
      (return-from check-regularity nil))
    ;;
    (with-in-module (module)
      (unless silent
	(let ((*print-indent* (+ 2 *print-indent*)))
	  (declare (special *print-indent*))
	  (when empty-sorts
	    (with-output-simple-msg ()
	      (format t ">> The following sorts are empty:")
	      (dolist (s empty-sorts)
		(print-next)
		(print-sort-name s module))))
	  (when new-sorts
	    (with-output-simple-msg ()
	      (format t ">> The following sorts may be required for regularity:")
	      (dolist (s new-sorts)
		(let ((subs (reg-direct-subsorts s (module-sort-order module))))
		  (print-next)
		  (princ "[ ")
		  (when subs
		    (dolist (s subs)
		      (print-sort-name s module)
		      (princ " "))
		    (princ "< "))
		  (print-sort-name s)
		  (princ " <")
		  (dolist (x (and-sort-components s))
		    (princ " ")
		    (print-sort-name x module))
		  (princ " ]")))))
	  (when new-methods
	    (with-output-simple-msg ()
	      (format t ">> The following operators may be required for regularity:")
	      (dolist (m new-methods)
		(print-next)
		(reg-report-method m module))))
	  (when redundant-methods
	    (with-output-simple-msg ()
	      (format t ">> The following operators are detected as redundant,")
	      (format t "~%   due to the above new operators.")
	      (dolist (m redundant-methods)
		(print-next)
		(reg-report-method m module))))
	  (when empty-methods
	    (with-output-simple-msg ()
	      (format t ">> The following operators have empty arity:")
	      (dolist (m empty-methods)
		(print-next)
		(reg-report-method m module)))))))
    ;; was not regular
    t))


;;; EOF
