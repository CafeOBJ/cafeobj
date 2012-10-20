;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: index.lisp,v 1.3 2007-09-22 10:25:50 sawada Exp $
;;;
(in-package :chaos)
#|=============================================================================
			     System:Chaos
			    Module:BigPink
			  File:index.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;                           **********
;;;			       INDEXING
;;;                           **********

;;; ==========================
;;; INDEX TABLE
;;; (Hash Table)
;;; ==========================

;;; ----------
;;; PRIMITIVES
;;; ----------

;;; general data structure

(defmacro make-index-table ()
  `(make-hash-table :test #'eq))

(defmacro make-entry-in-index-table (table key)
  `(setf (gethash ,key ,table) nil))

(defmacro index-table-count (table)
  `(hash-table-count ,table))

(defmacro set-to-index-table (table key item)
  `(setf (gethash ,key ,table) ,item))

(defmacro add-to-index-table (table key item &optional test)
  (if test
      `(pushnew ,item (gethash ,key ,table) :test ,test)
    `(push ,item (gethash ,key ,table))))

(defmacro delete-from-index-table (table key)
  `(remhash ,key ,table))

(defmacro get-indexed-data (table key)
  `(gethash ,key ,table))

(defun clear-all-index-tables (&optional (clear-demod t))
  (clrhash *pos-literals*)
  (clrhash *neg-literals*)
  (clrhash *clash-pos-literals*)
  (clrhash *clash-neg-literals*)
  (clrhash *paramod-rules*)
  (clrhash *parainto-var-rules*)
  (clrhash *parafrom-var-rules*)
  (clrhash *full-lit-table*)
  (clrhash *clash-lit-table*)
  (when (and *demodulators* clear-demod)
    (clrhash *demodulators*))
  )

;;;
;;; SPECIALIZE-TERM
;;;
(defun specialize-term (term module)
  (declare (type term term)
	   (type module module))
  (let* ((method (if (term-is-applform? term)
		     (term-head term)
		   nil))
	 (mmod (if method (method-module method) nil))
	 (promod (if *ignore-protected-modules*
		     nil
		   (module-protected-modules module)))
	 (opinfo-table (module-opinfo-table module))
	 (result nil))
    (declare (type (or null method method))
	     (type module)
	     (type (or null module) mmod promod)
	     (type hash-table opinfo-table)
	     (type list result))
    ;;
    (unless (term-is-variable? term)
      (setq result
	(specialize-term-for-methods
	 term
	 (if (method-is-universal method)
	     (method-lower-methods method opinfo-table)
	   (remove-if #'(lambda (meth)
			  (let ((xmod (method-module meth)))
			    (and (not (eq xmod mmod))
				 (if (assq mmod (module-all-submodules xmod))
				     (memq mmod (module-protected-modules xmod))
				   (memq xmod promod)))))
		      (method-lower-methods method opinfo-table)))
       module)))
    result ))
  
(defun get-all-methods-of-sort (sort module)
  (declare (type sort* sort)
	   (type module module))
  (let ((so (module-sort-order module))
	(res nil))
    (dolist (info (module-all-operators module))
      (dolist (m (opinfo-methods info))
	(unless (eq *void-method* m)
	  (when (sort<= (method-coarity m) sort so)
	    (push m res)))))
    res))

(defun specialize-term-for-methods (term methods mod)
  (declare (type term term)
	   (type list methods)
	   (type module mod))
  (let ((res nil))
    (dolist (method methods)
      (declare (type method method))
      (when (rule-check-down mod method (term-subterms term))
	(push method res)))
    #||
    (dolist (sub (term-subterms term))
      (if (term-is-variable? sub)
	  (setq res
	    (nconc res (get-all-methods-of-sort (variable-sort sub) mod)))
	(let ((meth (term-head sub)))
	  (push meth res)
	  (setq res
	    (nconc res
		   (method-lower-methods meth (module-opinfo-table mod)))))
	))
    ||#
    ;;
    res))

;;; construct key for getting 
;;;

(declaim (inline pn-const-pat))

(defun pn-const-pat (atom)
  (declare (type (or term sort*) atom)
	   (values (or sort* method)))
  (if (sort-p atom)
      atom
    (if (term-is-variable? atom)
	(variable-sort atom)
      (term-head atom))))

;;; construct keys for adding/deleting pattern
;;;
(declaim (inline pn-const-possible-pat))

(defun pn-const-possible-pat (atom module &optional full)
  (declare (type term atom)
	   (type module module)
	   (type boolean full))
  (if (term-is-variable? atom)
      (sub-or-equal-sorts (term-sort atom) (module-sort-order module))
    (let ((ops (if full
		   (term-operators atom)
		 (list (term-head atom))))
	  (opinfo-table (module-opinfo-table module))
	  (ans nil))
      (declare (type list ops)
	       (type hash-table opinfo-table)
	       (type list ans))
      (dolist (op ops)
	(declare (type method op))
	(push op ans)
	(dolist (m (method-lower-methods op opinfo-table))
	  (pushnew m ans :test #'eq)))
      ans)))

;;; literal entry : literal
;;;
(defmacro literal-entry-literal (lent) lent)

(defmacro literal-entry-atom (lent)
  `(literal-atom ,lent))

;;;
;;; GET-LITERAL-ENTRY-FROM-ATOM
;;;
(declaim (inline get-literal-entry-from-atom))

(defun get-literal-entry-from-atom (db atom)
  (declare (type hash-table db) (type term atom)
	   (values list))
  (get-indexed-data db (pn-const-pat atom)))

(declaim (inline add-literal-to-table))

(defun add-literal-to-table (table lit &optional full)
  (declare (type hash-table table)
	   (type literal lit)
	   (type boolean full))
  (let ((keys (pn-const-possible-pat (literal-atom lit) *current-module* full)))
    (declare (type list keys))
    (dolist (key keys)
      (add-to-index-table table key lit))))

(declaim (inline delete-literal-from-table))

(defun delete-literal-from-table (table lit &optional full)
  (declare (type hash-table table)
	   (type literal lit)
	   (type boolean full))
  (let ((keys (pn-const-possible-pat (literal-atom lit) *current-module* full)))
    (dolist (key keys)
      (let ((new-data)
	    (lit-ent (get-indexed-data table key)))
	(dolist (l lit-ent)
	  (unless (eq l lit)
	    (push l new-data)))
	(set-to-index-table table key new-data)))
    t))

(declaim (inline delete-literal-from-table-slow))

(defun delete-literal-from-table-slow (table lit)
  (declare (type hash-table table)
	   (type literal lit))
  (maphash #'(lambda (key data)
	       (declare (type list data))
	       (setf (gethash key table)
		 (delete lit data :test #'eq)))
	   table))

;;; ---------------------------------------
;;; SPECIALIZED TABLE FUNCTIONS for CLAUSE
;;; ---------------------------------------

(defun add-clause-to-table (table clause)
  (declare (type hash-table table)
	   (type clause clause))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (add-literal-to-table table lit)))

(defun delete-clause-from-table (table clause)
  (declare (type hash-table table)
	   (type clause clause))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (delete-literal-from-table table lit)))


;;; ==================
;;; INDEXING FUNCTIONS
;;; ==================

;;; we use the following tables for inference, back subsumption,
;;; paramodulations, etc...

(defun pignose-index-all (module)
  (declare (type module module))
  ;; (clear-all-index-tables nil)
  (let ((psys (module-proof-system module)))
    (declare (type psystem psys))
    (dolist (cl (psystem-usable psys))
      (declare (type clause cl))
      (index-clash-literals cl)
      (index-all-literals cl))
    (dolist (cl (psystem-sos psys))
      (declare (type clause cl))
      (index-all-literals cl))
    (dolist (cl (psystem-passive psys))
      (declare (type clause cl))
      (index-all-literals cl))
    ))

;;; INDEX SUBSUME TREE ----------------------------------------------

;;; -----
;;; NLIST
;;; list with its length

;;; create a new, empty nlist
(defmacro make-empty-nlist ()
  `(cons 0 nil))

;;; the number of elements in an nlist.
(defmacro nlist-n (x)
  `(car ,x))

;;; the elements in a nlist.
(defmacro nlist-list (x)
  `(cdr ,x))

;;; add a new element to an nlist
(defun nlist-push (item nlist)
  (incf (car nlist))
  (push item (cdr nlist))
  nlist)

;;; -----
;;; DTREE : discrimiation tree
;;; 
(defstruct (dtree (:type vector))
  (first nil)
  (rest nil)
  (atoms nil)
  (var (make-empty-nlist)))

(defmacro get-dtree (key hash)
  (once-only (key hash)
	     `(or (gethash ,key ,hash)
		  (let ((new-ent (make-dtree)))
		    (setf (gethash ,key ,hash) new-ent)
		    new-ent))))

(defun is-insert (literal itable)
  (let ((atom (literal-atom literal)))
    (dtree-index atom literal (get-dtree (term-head atom) itable))
    ))

(defun dtree-index (key value dtree)
  (flet ((lookup (atom dtree)
	   (or (cdr (assoc atom (dtree-atoms dtree)))
	       (let ((new (make-empty-nlist)))
		 (push (cons atom new) (dtree-atoms dtree))
		 new))))
    (cond ((null key))
	  ((atom key)		; method/built-in value
	   (nlist-push value (lookup key dtree)))
	  ((not (termp key))
	   (dtree-index (first key) value
			(or (dtree-first dtree)
			    (setf (dtree-first dtree) (make-dtree))))
	   (dtree-index (rest key) value
			(or (dtree-rest dtree)
			    (setf (dtree-rest dtree) (make-dtree))))
	   )
	  ((term-is-applform? key)
	   (dtree-index (term-head key)
			value
			(or (dtree-first dtree)
			    (setf (dtree-first dtree) (make-dtree))))
	   (when (term-subterms key)
	     (unless (dtree-rest dtree)
	       (setf (dtree-rest dtree) (make-dtree)))
	     (dtree-index (term-subterms key) value (dtree-rest dtree))))
	  ((term-is-variable? key)
	   (nlist-push value (dtree-var dtree)))
	  ((term-is-builtin-constant? key)
	   (dtree-index (term-builtin-value key) value
			(or (dtree-first dtree)
			    (setf (dtree-first dtree) (make-dtree))))
	   ;;(nlist-push value (lookup (term-builtin-value key) dtree))
	   )
	  (t (break "illegal key"))
	  ))
  )

;;; IS-FETCH
;;; returns a list of buckets potentialy matching the given term.
;;;
(defun is-fetch (term is-table)
  (dtree-fetch term (get-dtree (term-head term) is-table)
	       nil 0 nil most-positive-fixnum))

(defmacro foreach-dentry ((var dtree-ent) &body body)
  `(dolist (xent ,dtree-ent)
     (dolist (,var xent)
       ,@body)))

(defun is-fetch-concat (term is-table)
  (let ((res nil))
    (foreach-dentry (e (is-fetch term is-table))
		    (push e res))
    #||
    (with-output-simple-msg ()
      (princ "fetch concat: ")
      (term-print term)
      (dolist (x res)
	(print-next)
	(prin1 x)))
    ||#
    (nreverse res)))

;;; DTREE-FETCH
;;; returns two values:
;;; 1. a list-of-lists of possible matches to pat.
;;; 2. number of elements in the list-of-lists.
;;;
(defun dtree-fetch (pat dtree var-list-in var-n-in best-list best-n)
  (if (or (null dtree)
	  (null pat)
	  (and (termp pat) (term-is-variable? pat)))
      (values best-list best-n)
    (let* ((var-nlist (dtree-var dtree))
 	   (var-n (+ var-n-in (nlist-n var-nlist)))
	   (var-list (if (null (nlist-list var-nlist))
			 var-list-in
		       (cons (nlist-list var-nlist)
			     var-list-in))))
      (cond ((>= var-n best-n) (values best-list best-n))
	    ((atom pat)
	     (dtree-atom-fetch pat
			       dtree
			       var-list
			       var-n
			       best-list
			       best-n))
	    ((not (termp pat))
	     (multiple-value-bind (list1 n1)
		 (dtree-fetch (first pat)
			      (dtree-first dtree)
			      var-list
			      var-n
			      best-list
			      best-n)
	       (dtree-fetch (rest pat)
			    (dtree-rest dtree)
			    var-list
			    var-n
			    list1
			    n1)))
	    (t (multiple-value-bind (list1 n1)
		   (if (term-is-builtin-constant? pat)
		       (dtree-fetch (term-builtin-value pat)
				    (dtree-first dtree)
				    var-list
				    var-n
				    best-list
				    best-n)
		     (dtree-fetch (term-head pat)
				  (dtree-first dtree)
				  var-list
				  var-n
				  best-list
				  best-n))
		 (dtree-fetch (term-subterms pat)
			      (dtree-rest dtree)
			      var-list
			      var-n
			      list1
			      n1))))
      )))

(defun dtree-atom-fetch (op dtree var-list var-n best-list best-n)
  #||
  (unless dtree
    (return-from dtree-atom-fetch (values var-list var-n))
    )
  ||#
  ;;
  (let ((atom-nlist (cdr (assoc op (dtree-atoms dtree)))))
    (cond ((or (null atom-nlist) (null (nlist-list atom-nlist)))
	   (values var-list var-n)
	   )
	  ((and atom-nlist (< (incf var-n (nlist-n atom-nlist)) best-n))
	   (values (cons (nlist-list atom-nlist) var-list) var-n))
	  (t (values best-list best-n))
	  )))


;;; IS-DELETE
;;;
(defun dtree-delete (key value dtree test)
  (flet ((lookup (atom dtree)
	   (cdr (assoc atom (dtree-atoms dtree))))
	 (nlist-delete (nlist)
	   (when nlist
	     (decf (car nlist))
	     (setf (cdr nlist)
	       (delete value (cdr nlist) :count 1 :test test))
	     nlist)))
    (when dtree
      (cond ((null key))
	    ((atom key)
	     (let ((nlist (lookup key dtree)))
	       (when nlist
		 (nlist-delete (lookup key dtree)))))
	    ((not (termp key))
	     (dtree-delete (first key)
			   value
			   (dtree-first dtree)
			   test)
	     (dtree-delete (rest key)
			   value
			   (dtree-rest dtree)
			   test))
	    ((term-is-applform? key)
	     (dtree-delete (term-head key)
			   value
			   (dtree-first dtree)
			   test)
	     (dtree-delete (term-subterms key) value (dtree-rest dtree)
			   test))
	    ((term-is-variable? key)
	     (dolist (ns (dtree-atoms dtree))
	       (nlist-delete ns))
	     (nlist-delete (dtree-var dtree)))
	    ((term-is-builtin-constant? key)
	     (dtree-delete value (term-builtin-value key)
			   (dtree-first dtree)
			   test)
	     ;; (nlist-delete value (lookup (term-builtin-value key) dtree))
	     )
	    (t (break "illegal key"))
	    ))
    ))

(defun is-delete (literal itable &optional (test #'eql))
  (let ((atom (literal-atom literal)))
    (dtree-delete atom literal (get-dtree (term-head atom) itable)
		  test)
    ))

;;; INDEX-ALL-LITERALS : Clause -> Void
;;;
;;; make indexed table for forward subsumption, back subsumption,
;;; and unit conflict.
;;;  positive literals are registered into *pos-literals*, and
;;;  negative literals are registered into *neg-literals*.
;;;
#||
(defun index-all-literals (cl)
  (declare (type clause cl))
  (when (= -1 (clause-id cl))
    ;; not yet registered nor indexed.
    ;; (register-clause cl *current-psys*)
    (let ((c2 nil))
      (when (and (eq (clause-container cl) :passive)
		 (unit-clause? cl)
		 )
	(let ((lit (ith-literal cl 1)))
	  (when (eq-literal? lit)
	    (setq c2 (copy-clause cl))
	    ;; (register-clause c2 *current-psys*)
	    (setf (clause-parents c2)
	      (list (list :copy-rule (clause-id cl)
			  :flip-eq-rule
			  )))
	    (setq lit (ith-literal c2 1))
	    (let* ((atom (literal-atom lit))
		   (new-atom (make-term-with-sort-check *fopl-eq*
							(list (term-arg-2 atom)
							      (term-arg-1 atom)))))
	      (setf (literal-atom lit) new-atom))))
	)
      (dolist (lit (if c2
		       (append (clause-literals cl)
			       (clause-literals c2))
		     (clause-literals cl)))
	(declare (type literal lit))
	(unless (answer-literal? lit)
	  (when (and (pn-flag back-demod)
		     (not (eq (clause-container cl) :passive)))
	    (add-literal-to-table *full-lit-table* lit t))
	  (cond ((positive-literal? lit)
		 ;; (add-literal-to-table *pos-literals* lit)
		 (is-insert lit *pos-literals*)
		 )
		(t
		 ;; (add-literal-to-table *neg-literals* lit)
		 (is-insert lit *neg-literals*)
		 ))))
      )))
||#

(defun index-all-literals (cl)
  (declare (type clause cl))
  (let ((c2 nil))
    (when (and (eq (clause-container cl) :passive)
	       (unit-clause? cl))
      (let ((lit (ith-literal cl 1)))
	(when (and (eq-literal? lit)
		   ;;
		   (pn-flag eq-literals-both-ways)
		   ;;
		   )
	  (setq c2 (copy-clause cl))
	  (setf (clause-parents c2)
	    (list (list :copy-rule (clause-id cl)
			:flip-eq-rule
			)))
	  (setq lit (ith-literal c2 1))
	  (let* ((atom (literal-atom lit))
		 (new-atom (make-term-with-sort-check *fopl-eq*
						      (list (term-arg-2 atom)
							    (term-arg-1 atom)))))
	    (setf (literal-atom lit) new-atom))))
      )
    (dolist (lit (if c2
		     (append (clause-literals cl)
			     (clause-literals c2))
		   (clause-literals cl)))
      (declare (type literal lit))
      (unless (answer-literal? lit)
	(when (and (pn-flag back-demod)
		   (not (eq (clause-container cl) :passive)))
	  (add-literal-to-table *full-lit-table* lit t))
	(cond ((positive-literal? lit)
	       ;; (add-literal-to-table *pos-literals* lit)
	       (is-insert lit *pos-literals*)
	       )
	      (t
	       ;; (add-literal-to-table *neg-literals* lit)
	       (is-insert lit *neg-literals*)
	       ))))
    ))

;;; UN-IDEX-ALL-LITERALS : Clause -> Void
;;;
(defun un-index-all-literals (clause)
  (declare (type clause clause))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (when (pn-flag back-demod)
      (delete-literal-from-table *full-lit-table* lit t))
    (unless (answer-literal? lit)
      (cond ((positive-literal? lit)
	     ;; (delete-literal-from-table *pos-literals* lit)
	     (is-delete lit *pos-literals*)
	     )
	    (t
	     ;; (delete-literal-from-table *neg-literals* lit)
	     (is-delete lit *neg-literals*)
	     )
	    ))))
  
(defun un-index-all-literals-slow (clause)
  (declare (type clause clause))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (when (pn-flag back-demod)
      (delete-literal-from-table-slow *full-lit-table* lit))
    (unless (answer-literal? lit)
      (cond ((positive-literal? lit)
	     ;; (delete-literal-from-table-slow *pos-literals* lit)
	     (is-delete lit *pos-literals*)
	     )
	    (t
	     ;; (delete-literal-from-table-slow *neg-literals* lit)
	     (is-delete lit *neg-literals*)
	     )
	    ))
    ))

;;; INDEX-CLASH-LITERALS
;;; make entries of literals for inference rules, and index terms for
;;; paramodulation.
;;;
(defun index-clash-literals (c)
  (declare (type clause c))
  (dolist (lit (clause-literals c))
    (declare (type literal lit))
    (unless (answer-literal? lit)
      ;; register to clash tables
      (if (positive-literal? lit)
	  ;; (add-literal-to-table *clash-pos-literals* lit)
	  (is-insert lit *clash-pos-literals*)
	;; (add-literal-to-table *clash-neg-literals* lit)
	(is-insert lit *clash-neg-literals*)
	)
      (when (or (pn-flag para-from) (pn-flag para-into))
	;; register to paramod table
	(index-paramodulation lit))))
  )

;;; UN-INDEX-CLASH-LITERALS
;;;
(defun un-index-clash-literals (c)
  (declare (type clause c))
  (dolist (lit (clause-literals c))
    (declare (type literal lit))
    (unless (answer-literal? lit)
      (if (positive-literal? lit)
	  ;; (delete-literal-from-table *clash-pos-literals* lit)
	  (is-delete lit *clash-pos-literals*)
	;; (delete-literal-from-table *clash-neg-literals* lit)
	(is-delete lit *clash-neg-literals*)
	)
      (when (or (pn-flag para-from) (pn-flag para-into))
	(un-index-paramodulation lit))))
  )

(defun un-index-clash-literals-slow (c)
  (declare (type clause c))
  (dolist (lit (clause-literals c))
    (declare (type literal lit))
    (unless (answer-literal? lit)
      (if (positive-literal? lit)
	  ;; (delete-literal-from-table-slow *clash-pos-literals* lit)
	  (is-delete lit *clash-pos-literals*)
	;; (delete-literal-from-table-slow *clash-neg-literals* lit)
	(is-delete lit *clash-neg-literals*)
	)
      (when (or (pn-flag para-from) (pn-flag para-into))
	(un-index-paramodulation-slow lit)
	)))
  )

;;; =====================
;;; PARAMODULATION TABLES
;;; =====================

(defun get-paramod-entry (key table)
    (if (term-is-variable? key)
	(get-dtree (variable-sort key) table)
      (get-dtree (term-head key) table)))

(defun is-paramod-insert (lhs paramod itable)
  (flet ((insert-from-var-pat (sort)
	   (push paramod (gethash sort *parafrom-var-rules*)))
	 (insert-to-var-pat (sort)
	   (push paramod (gethash sort *parainto-var-rules*)))
	 )
    (if (term-is-variable? lhs)
	(insert-from-var-pat (variable-sort lhs))
      (progn
	(dtree-index lhs paramod (get-paramod-entry lhs itable))
	(when (pn-flag para-into-vars)
	  (insert-to-var-pat (term-sort lhs))))
      )))

(defun is-paramod-delete (lhs literal itable)
  (flet ((delete-into-var-pat (sort)
	   (let ((ent (gethash sort *parainto-var-rules*)))
	     (setf (gethash sort *parainto-var-rules*)
	       (delete literal ent
		       :test #'(lambda (x y)
				 (eq x (paramod-literal y)))))))
	 (delete-from-var-pat (sort)
	   (let ((ent (gethash sort *parafrom-var-rules*)))
	     (setf (gethash sort *parafrom-var-rules*)
	       (delete literal ent
		       :test #'(lambda (x y)
				 (eq x (paramod-literal y))))))))
    (if (term-is-variable? lhs)
	(delete-from-var-pat (variable-sort lhs))
      (progn
	(dtree-delete lhs literal (get-paramod-entry lhs itable)
		      #'(lambda (x y)
			  (eq x (paramod-literal y))))
	(when (pn-flag para-into-vars)
	  (delete-into-var-pat (term-sort lhs)))
	))))

(defun is-paramod-fetch (term itable)
  (if (term-is-variable? term)
      (list (gethash (variable-sort term) *parainto-var-rules*))
    (dtree-fetch term (get-paramod-entry term itable)
		 nil 0 nil most-positive-fixnum)))

(defun is-paramod-fetch-concat (term itable)
  (let ((res nil))
    (foreach-dentry (e (is-paramod-fetch term itable))
		    (push e res))
    (when (pn-flag para-from-vars)
      (dolist (para (gethash (term-sort term)
			     *parafrom-var-rules*))
	(push para res)))
    (nreverse res)))

(defun add-eq-literal (table lhs rhs lit)
  (declare (type hash-table table)
	   (type term lhs rhs)
	   (type literal lit))
  (unless (or ;; (term-is-builtin-constant? lhs)
	      (term-is-lisp-form? lhs))

    (when (and (term-is-variable? lhs)
	       (not (pn-flag para-into-vars)))
      (return-from add-eq-literal nil))

    (when (and (term-is-applform? lhs)
	       (pn-flag para-skip-skolem)
	       (is-skolem (term-head lhs)))
      (return-from add-eq-literal nil))
    ;;
    (let ((paramod (make-paramod :lhs lhs
				 :rhs rhs
				 :literal lit)))
      ;;
      #||
      (let ((keys (pn-const-possible-pat lhs *current-module*)))
	(dolist (key keys)
	  (add-to-index-table table
			      key
			      paramod))

	t)
      ||#
      (is-paramod-insert lhs paramod table)
      )))

#||
(defun add-eq-literal-to-table (table lit)
  (declare (type hash-table table)
	   (type literal lit))
  (let* ((atom (literal-atom lit))
	 (lhs (term-arg-1 atom))
	 (rhs (term-arg-2 atom)))
    (declare (type term atom lhs rhs))
    (when (or (not (pn-flag para-from-units-only))
	      (unit-clause? (literal-clause lit)))
      (when (pn-flag para-into-left)
	(if (pn-flag para-from-left)
	    (if (or (pn-flag para-from-vars)
		    (not (term-is-variable? lhs)))
		(add-eq-literal table lhs rhs lit))
	  (if (pn-flag para-from-right)
	      (if (or (pn-flag para-from-vars)
		      (not (term-is-variable? rhs)))
		  (add-eq-literal table rhs lhs lit))))
	))))
||#

(defun add-eq-literal-to-table (table lit)
  (declare (type hash-table table)
	   (type literal lit))
  (let* ((atom (literal-atom lit))
	 (lhs (term-arg-1 atom))
	 (rhs (term-arg-2 atom)))
    (declare (type term atom lhs rhs))
    (when (or (not (pn-flag para-from-units-only))
	      (unit-clause? (literal-clause lit)))
      (when (pn-flag para-from-left)
	(if (or (pn-flag para-from-vars)
		(not (term-is-variable? lhs)))
	    (add-eq-literal table lhs rhs lit)))
      (when (pn-flag para-from-right)
	(if (or (pn-flag para-from-vars)
		(not (term-is-variable? rhs)))
	    (add-eq-literal table rhs lhs lit))))
    ))

(defun delete-eq-literal-from-table (table lit)
  (declare (type hash-table table)
	   (type literal lit))
  (let ((atom (literal-atom lit)))
    (declare (type term atom))
    (let ((lhs (term-arg-1 atom))
	  (rhs (term-arg-2 atom)))
      (declare (type term lhs rhs))
      (when (pn-flag para-into-left)
	(delete-eq-literal-atom-from-table table lhs lit))
      (when (pn-flag para-into-right)
	(delete-eq-literal-atom-from-table table rhs lit)))))

(defun delete-eq-literal-from-table-slow (table lit)
  (declare (type hash-table table)
	   (type literal lit))
  (maphash #'(lambda (key data)
	       (declare (type list data))
	       (setf (gethash key table)
		 (delete-if #'(lambda (x)
				(eq lit (paramod-literal x)))
			    data)))
	   table))

#||
(defun delete-eq-literal-atom-from-table (table term lit)
  (declare (type hash-table table)
	   (type term term)
	   (type literal lit))
  (when (term-is-variable? term)
    (unless (pn-flag para-into-vars)
      (return-from delete-eq-literal-atom-from-table nil)))
  (let ((keys (pn-const-possible-pat term *current-module*)))
    (dolist (key keys)
      (let ((new-data nil))
	(dolist (paramod (get-indexed-data table key))
	  (unless (eq lit (paramod-literal paramod))
	    (push paramod new-data)))
	(set-to-index-table table key new-data)))
    t))
||#

(defun delete-eq-literal-atom-from-table (table term lit)
  (declare (type hash-table table)
	   (type term term)
	   (type literal lit))
  (when (term-is-variable? term)
    (unless (pn-flag para-into-vars)
      (return-from delete-eq-literal-atom-from-table nil)))
  (is-paramod-delete term lit table))

;;; INDEX-PARAMODULATION : Literal
;;;
(defun index-paramodulation (lit)
  (declare (type literal lit))
  ;; for from paramodulation
  (add-literal-to-table *clash-lit-table* lit t)

  ;; for into paramodulation
  (unless (positive-eq-literal? lit)
    (return-from index-paramodulation nil))
  ;;
  (let* ((atom (literal-atom lit))
	 (lhs (term-arg-1 atom))
	 (rhs (term-arg-2 atom)))
    (when (term-is-identical lhs rhs)
      (return-from index-paramodulation nil))
    ;;
    (add-eq-literal-to-table *paramod-rules*
			     lit)))


;;; UN-INDEX-PARAMODULATION : Literal
;;;
(defun un-index-paramodulation (lit)
  (declare (type literal lit))
  ;;
  (delete-literal-from-table *clash-lit-table* lit t)
  ;;
  (unless (eq-literal? lit)
    (return-from un-index-paramodulation nil))
  (let* ((atom (literal-atom lit))
	 (lhs (term-arg-1 atom))
	 (rhs (term-arg-2 atom)))
    (declare (type term atom lhs rhs))
    (when (term-is-identical lhs rhs)
      (return-from un-index-paramodulation nil))
    (delete-eq-literal-from-table *paramod-rules* lit))
  )

(defun un-index-paramodulation-slow (lit)
  (declare (type literal lit))
  (delete-literal-from-table-slow *clash-lit-table* lit)
  (unless (eq-literal? lit)
    (return-from un-index-paramodulation-slow nil))
  ;; (delete-eq-literal-from-table-slow *paramod-rules* lit)
    (let* ((atom (literal-atom lit))
	 (lhs (term-arg-1 atom))
	 (rhs (term-arg-2 atom)))
      (declare (type term atom lhs rhs))
      (when (term-is-identical lhs rhs)
	(return-from un-index-paramodulation-slow nil))
      (delete-eq-literal-from-table *paramod-rules* lit))
  )

;;; ============
;;; DEMODULATORS
;;; ============

(defun get-all-demodulators (hash &optional sort)
  (declare (type hash-table hash)
	   (type boolean sort))
  (flet ((!clause-id (cl)
	   (if (clause-p cl)
	       (clause-id cl)
	     0)))
    (let ((res nil))
      (declare (type list res))
      (maphash #'(lambda (key demod)
		   (declare (ignore key))
		   (dolist (d demod)
		     (pushnew d res :test #'eq)))
	       hash)
      (if sort
	  (sort res #'(lambda (x y) (< (!clause-id (demod-clause x))
				       (!clause-id (demod-clause y)))))
	res))))

(defun un-index-demodulator (clause)
  (declare (type clause clause))
  (let ((xdeleted nil))
    (declare (type boolean xdeleted))
    (maphash #'(lambda (key demods)
		 (let ((new-ent nil)
		       (deleted nil))
		   (dolist (demod demods)
		     (declare (type demod demod))
		     (if (eq (demod-clause demod) clause)
			 (setq deleted t)
		       (push demod new-ent)))
		   (when deleted
		     (setq xdeleted t)
		     (setf (gethash key *demodulators*) new-ent))))
	     *demodulators*)
    (when xdeleted
      (decf (pn-stat demodulators-size)))
    ))

;;; ==================
;;; INDEX TABLE UTILS
;;; ==================

;;; TABLE-TO-CLAUSE-LIST
;;;
(defun table-to-clause-list (db)
  (declare (type hash-table db)
	   (values list))
  (let ((clauses nil))
    (maphash #'(lambda (x y)
		 (declare (ignore x))
		 (dolist (data y)
		   (let ((lit (literal-entry-literal data)))
		     (declare (type literal lit))
		     (pushnew (literal-clause lit) clauses :test #'eq))))
	     db)
    clauses))

;;; TABLE-TO-LITERAL-LIST
;;;
(defun table-to-literal-list (db)
  (declare (type hash-table db)
	   (values list))
  (let ((lits nil))
    (declare (type list lits))
    (maphash #'(lambda (x y)
		 (declare (ignore x))
		 (dolist (data y)
		   (pushnew (literal-entry-literal data) lits
			    :test #'eq)))
	     db)
    lits))

;;; GET-CLAUSES-FROM-TABLE
;;; *** NOTE: now this is used for backsubsume only.

(defun get-clashable-clauses-from-literal (db literal &optional (opt nil))
  (declare (type hash-table db)
	   (type literal literal)
	   (type boolean opt)
	   (ignore opt)
	   (values list))
  (let ((res nil)
	(atom (literal-atom literal))
	)
    (declare (type list res)
	     (type term atom))
    ;;
    (dolist (litent (is-fetch atom db))
      (dolist (lit litent)
	(pushnew (literal-clause lit)
		 res
		 :test #'eq)))
    ;; (setq res (delete-duplicates (mapcar #'literal-clause
    ;;					 (is-fetch-all atom db))))
    ;;
    #||
    (with-output-simple-msg ()
      (princ "** clashable for lit ")
      (pr-literal literal *standard-output*)
      (print-next)
      (pr-clause-list res))
    ||#
    ;;
    res
    ))

;;; ** NOTE : this is used for back demodulation & from paramodulation
;;;
(defun get-clashable-clauses-from-atom (db atom &optional (opt nil))
  (declare (type hash-table db)
	   (type term atom)
	   (type boolean opt)
	   (values list))
  (let ((res nil)
	(key (if (and opt (eq (term-head atom) *fopl-eq*))
		 (or (and (not (term-is-variable? (term-arg-1 atom)))
			  (term-arg-1 atom))
		     (and (not (term-is-variable? (term-arg-2 atom)))
			  (term-arg-2 atom))
		     atom)
	       atom)))
    (declare (type list res)
	     (type term key))
    (dolist (data (get-literal-entry-from-atom db key))
      (pushnew (literal-clause (the literal (literal-entry-literal data)))
	       res
	       :test #'eq))
    res))

;;; EOF
