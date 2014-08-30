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
				 System: CHAOS
			       Module: construct
				File: sort.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;=============================================================================
;;;				      SORT
;;;=============================================================================

;;; (defvar *on-sort-debug* nil)

;;; ************
;;; CONSTRUCTORS _______________________________________________________________
;;; ************

;;; Currently we implement identifiers as Lisp symbols.

(defmacro make-sort-id (symbol__$$)
  (once-only (symbol__$$)
    ` (if (stringp ,symbol__$$)
	  (intern ,symbol__$$)
	  ,symbol__$$)))

(defun add-sort-to-module (sort mod)
  ;; register sort in module
  (when (eq mod (sort-module sort))
    (pushnew sort (module-own-sorts mod) :test #'eq))
  (symbol-table-add (module-symbol-table mod) (sort-id sort) sort)
  (when *on-sort-debug*
    (with-output-msg ()
      (format t "adding sort ~s(~s)" (sort-id sort) sort)
      (print-next)
      (princ " to module ")
      (print-chaos-object mod)))
  (pushnew sort (module-all-sorts mod) :test #'eq)
  ;; make entry in sort-relations of module & sort-order.
  ;; * this is very important *
  (adjoin-sort-relation (make-sort-relation sort) mod)
  (add-relation-to-order (make-sort-relation sort) (module-sort-order mod))
  ;; set status mark
  (mark-need-parsing-preparation mod)
  )

;;; DEFINE-SORT : name module -> sort
;;; make new sort term if it not exist.
;;;
(defun define-sort (sort-id-symbol module
				   &optional
				   (type 'sort)
				   hidden
				   force)
  (declare (ignore force))
  (setq sort-id-symbol (make-sort-id sort-id-symbol))
  (let ((pre (find-sort-in module sort-id-symbol))
	 #||
	 (if force
	     nil
	   (simple-find-sort-in-local module sort-id-symbol))
	 ||#
	)
    #||
    (when (and (not force) pre)
      (with-output-chaos-warning ()
	(format t "sort ~s is already declared in the module "
		sort-id-symbol)
	(print-mod-name (sort-module pre))
	(print-next)
	(princ "...ignored.")
	(return-from define-sort nil)))
    ||#
    (if (and pre (eq (sort-type pre) type))
	(progn
	  (setf (sort-hidden pre) hidden)
	  pre)
	;;
	(let (sort)
	  (case type
	    (record-sort
	     (setf sort (new-record-sort sort-id-symbol module hidden))) 
	    (class-sort
	     (setf sort (new-class-sort sort-id-symbol module hidden)))
	    (sort
	     (setf sort (new-general-sort sort-id-symbol module hidden)))
	    (and-sort
	     (setf sort (new-and-sort sort-id-symbol module hidden)))
	    (or-sort
	     (setf sort (new-or-sort sort-id-symbol module hidden)))
	    (t (with-output-panic-message ()
		 (format t "Unsupported type of sort ~s!" type)
		 (chaos-error 'panic))))
	  ;; (register-sort sort)
	  sort))))

;;; DEFINE-BUILTIN-SORT

(defun define-builtin-sort (sort-id-symbol &optional
					   (module *chaos-module*)
					   (info nil)
					   (hidden nil)
					   (force nil))
  (setq sort-id-symbol (make-sort-id sort-id-symbol))
  (let ((pre (if force
		 nil
		 (simple-find-sort-in-local module sort-id-symbol)))
	sort)
    (if pre
	(setf sort pre)
	(setf sort (new-bi-sort sort-id-symbol module)))
    (setf (bsort-info sort) info)
    (setf (bsort-hidden sort) hidden)
    (add-builtin-sort sort module)
    sort))

;;; perform some additional house keeping work for builtin sort creation.

(defun add-builtin-sort (sort &optional (module *chaos-module*))
  ;; (register-sort sort)
  (register-builtin-sort sort)
  #||
  (when (eq module *chaos-module*)
    (setf (symbol-function
	   (intern (format nil
			   "THE-~A-SORT" (string-upcase (sort-print-name sort)))))
	  #'(lambda () sort)))
  ||#
  (add-sort-to-module sort module)
  sort)

;;; DEFINE-AND-SORT
;;;
(defun define-and-sort (sort-id-symbol module components &optional hidden)
  (setq sort-id-symbol (make-sort-id sort-id-symbol))
  (let ((pre (or (get-sort-named sort-id-symbol module)
		 (simple-find-sort-in-local module sort-id-symbol))))
    (if pre
	pre
	(let ((sort (new-and-sort sort-id-symbol module components hidden)))
	  (register-sort-cache sort)
	  sort))))

;;; DEFINE-OR-SORT
;;;
(defun define-or-sort (sort-id-symbol module components &optional hidden)
  (setq sort-id-symbol (make-sort-id sort-id-symbol))
  (let ((pre (or (get-sort-named sort-id-symbol module)
		 (simple-find-sort-in-local module sort-id-symbol))))
    (if pre
	pre
	(let ((sort (new-or-sort sort-id-symbol module components hidden)))
	  (register-sort-cache sort)
	  sort))))

;;; DEFINE-ERR-SORT
;;;
(defun define-err-sort (sort-id-symbol module components &optional subs hidden)
  (setq sort-id-symbol (make-sort-id sort-id-symbol))
  (let ((pre (or (get-sort-named sort-id-symbol module)
		 (simple-find-sort-in-local module sort-id-symbol))))
    (if pre
	pre
	(let ((sort (new-err-sort sort-id-symbol
				  module
				  components
				  subs
				  hidden)))
	  (register-sort-cache sort)
	  sort))))

;;; ******
;;; COPIER ____________________________________________________________________
;;; ******
;;; * TODO * 
;;; should I copy record/class's other slots?
;;;
(defun %copy-sort (sort module &optional new-name force)
  (let ((name (if new-name new-name (sort-id sort))))
    (let ((new-sort
	   (if (sort-is-builtin sort)
	       (define-builtin-sort name
		   module
		 (bsort-info sort)
		 (sort-is-hidden sort)
		 force)
	       (define-sort name
		   module
		 (sort-type sort)
		 (sort-is-hidden sort)
		 force))))
      ;;
      (setf (sort-derived-from new-sort) sort)
      ;;
      (cond ((memq (sort-type sort) '(class-sort record-sort))
	     ;;
	     (setf (crsort-is-a-copy new-sort) t)
	     ;; obsolate values, but for the future.....
	     (with-output-panic-message ()
	       (princ "sorry, but copying record/class sort is not yet properly supported!"))
	     )
	    ((eq (sort-type sort) 'and-sort)
	     (setf (and-sort-components new-sort)
		   (mapcar #'(lambda (s) (%copy-sort s module))
			   (and-sort-components sort)))
	     (with-output-chaos-warning ()
	       (princ "sorry, but copying `and-sort' is not yet properly supported!"))
	     )
	    ((eq (sort-type sort) 'or-sort)
	     (setf (or-sort-components new-sort)
		   (mapcar #'(lambda (s) (%copy-sort s module))
			   (or-sort-components sort)))
	     (with-output-chaos-warning ()
	       (princ "sorry, but copying `or-sort' is not yet properly supported!"))
	     ))
      ;;
      new-sort)))

;;; *********************
;;; SPECIAL SORT CREATORS ______________________________________________________
;;; *********************

;;; GLB-SORT s1 s2 module order
;;; Finds the GLB of given two sorts, if it does not exist create a sort which
;;; is the GLB, registering it to given order. 
;;;
;;; Ex.
;;;                      Bool          Natural
;;;                                     /  \
;;;                                    /    \
;;;                                   Zero  Posint
;;;
;;;   applying `glb-sort' to Bool and Natural will make the following
;;;
;;;                      Bool          Natural
;;;                        |        /   /  \
;;;                        |       /   /    \
;;;                        |      /   Zero  Posint
;;;     		   |     /
;;;                    Bool^Natural
;;;
(defun glb-sort (s1 s2
		    &optional
		    (module *current-module*)
		    (order *current-sort-order*)
		    )
  (cond ((sort<= s1 s2) s1)
	((sort< s2 s1) s2)
	(t (let ((meet (meet-of-sorts s1 s2 order))
		 sort)
	     (when (and (= 1 (length meet))
			(and-sort-p (car meet)))
	       ;; glb already exists. we don't need to create.
	       (return-from glb-sort (car meet)))
	     ;; creates GLB
	     (setq sort (make-glb-sort (list s1 s2) module))
	     (add-sort-to-module sort module)
	     #||
	     (setq sl (make-sort-relation sort
					  (remove-if #'(lambda (x) (sort= x sort)) meet)
					  (and-sort-components sort)))
	     ||#
	     (declare-subsort-in-module `((,@(remove-if #'(lambda (x) (sort= x sort)) meet)
					   :< ,sort :< ,@(and-sort-components sort)))
					module)
	     sort))))

;;; MAKE-GLB-SORT components join module order
;;;
(defun gather-and-components (sort)
  (let ((compo nil))
    (cond ((and-sort-p sort)
	   (setq compo (nconc compo
			      (mapcan #'(lambda (x)
					  (gather-and-components x))
				      (copy-list (and-sort-components sort))))))
	  (t (setq compo (nconc compo (list sort)))))
    compo))

(defun canonicalize-and-components (components sort-order)
  (let ((canon-compo nil))
    (dolist (compo components)
      (setq canon-compo (nconc canon-compo
			       (gather-and-components compo))))
    (minimal-sorts (delete-duplicates canon-compo :test #'eq)
		   sort-order)))
    
(defun glb-sort-name (sorts)
  (let ((compo-names (sort (mapcan #'(lambda (s)
				       (if (and-sort-p s)
					   (mapcar #'(lambda(x) (sort-id x))
						   (and-sort-components s))
					   (list (sort-id s))))
				   sorts)
			   #'(lambda (x y)
			       (string< (the simple-string (string x))
					(the simple-string (string y)))))))
    (setf compo-names (sort
		       (mapcar #'string
			       (delete-duplicates compo-names :test #'eq))
		       #'(lambda (id1 id2)
			   (string<= (the simple-string id1)
				     (the simple-string id2)))))
    (if (cdr compo-names)
	(intern (format nil "~{~^~A~^^~}" compo-names))
	(intern (format nil "^~A" (car compo-names))))))

(defun make-glb-sort (components &optional
				 (module *current-module*))
  (setq components (canonicalize-and-components components
						(module-sort-order module)))
  (let ((sort-id (glb-sort-name components))
	(glb nil))
    (setf glb (find-sort-in module sort-id))
    (if glb
	glb
	(define-and-sort sort-id module components))))

;;; JOIN-OF-SORTS sort1 sor2 order
;;;
(defun join-of-sorts (sort1 sort2 &optional (order *current-sort-order*))
  (cond ((sort= sort1 sort2) (list sort1))
	((sort< sort1 sort2 order) (list sort2))
	((sort< sort2 sort1 order) (list sort1))
	(t (minimal-sorts (intersection (supersorts sort1 order) (supersorts
								  sort2 order))
			  order))))

;;; LUB-SORT s1 s2 module-id order
;;; Finds LUB of s1 s2, if it does not exist, create the actual LUB which have
;;; given sorts as its direct supersorts, registering the created LUB to the
;;; given order.
;;;
;;; Ex.
;;;                      Bool          Natural
;;;                                     /  \
;;;                                    /    \
;;;                                   Zero  Posint
;;;
;;;   applying `lub-sort' to Bool and Natural will make the following
;;;
;;;                           Bool|Natural
;;;                           /         |
;;;			     /    	|
;;;                      Bool          Natural
;;;                                     /  \
;;;                                    /    \
;;;                                   Zero  Posint
;;;
;;;

(defmacro lub-sort-name (sorts____?)
  ` (intern (format nil "~{~^~A~^|~}"
		    (sort (mapcar #'(lambda (s) (string (sort-id s)))
				  ,sorts____?)
			  #'(lambda (id1 id2)
			      (declare (type simple-string id1 id2))
			      (string< id1 id2))))))

(defun lub-sort (s1 s2 &optional (module *current-module*) (order *current-sort-order*))
  (let ((join (join-of-sorts s1 s2 order)))
    (if (= 1 (length join))
	;; minimum exists. we don't nee to create.
	(return-from lub-sort (car join))
	;; creates the new one.
	(make-lub-sort (list s1 s2) join module))))

;;; MAKE-LUB-SORT components join module order

(defun make-lub-sort (components join
				 &optional
				 (module *current-module*))
  (let* ((sort-id (lub-sort-name components))
	 (lub (define-or-sort sort-id module components)))
    (add-sort-to-module lub module)
    (declare-subsort-in-module `((,@components :< ,lub ,@join)) module)
    lub))

;;; GENERATE-ERR-SORTS sort-order
;;; Generate err-sort at top of each connected component.
;;;
;;; Example:
;;;
;;;       NameRef       ObjectID      Number
;;;	     |           /| \    \      |
;;;          |         	/ |  \	  \ 	|
;;;          |         /  |   \	   \	|
;;;          Identifier	 ... String Integer
;;;
;;;  applying `generate-err-sorts' to this sort-order will make
;;;
;;;         ?:-NameRef+Number+ObjectID  ---  generated err-sort
;;;    	       /       	  |	     \
;;;	      / 	  |	      \
;;;	     /   	  |            \
;;;       NameRef       ObjectID      Number
;;;	     |           /| \    \      |
;;;          |         	/ |  \	  \ 	|
;;;          |         /  |   \	   \	|
;;;          Identifier	 ... String Integer
;;;
;;;
(defmacro make-err-sort-name (components____!?)
  ` (intern (format nil "?~{~^~A~^+~}"
		    (sort (mapcar #'(lambda (s) (string (sort-id s)))
				  ,components____!?)
			  #'(lambda (x y) (string< x y))))))

(defun generate-err-sorts (&optional (sort-order *current-sort-order*)
				     (module *current-module*))
  (flet ((find-the-equivalent-error-sort (id components olds)
	   (find-if #'(lambda (es)
			(let ((name (sort-id es)))
			  (and (eq id name)
			       (sort-set-equal (err-sort-components es)
					       components))))
		    olds))
	 )
    ;;
    (let ((old-errs (module-error-sorts module)) ; imported + generated.
	  (all-errors nil))		; the list of all error sort
					; newly generated.
      (declare (type list old-errs))
      ;; first, we clear all pre-defined error sorts.
      (clear-err-sorts sort-order)
    
      ;; maximal is the list of components top.
      ;; we now allow the non-filterd signature, ie, there can be multiple tops
      ;; for a connected component.
      (let ((maximal (maximal-sorts-no-error
		      (let ((res nil))
			(maphash #'(lambda (sort relation)
				     (declare (ignore relation))
				     (push sort res))
				 sort-order)
			res)
		      sort-order)))
	(while maximal
	  (let* ((s (car maximal))
		 (subs (sub-or-equal-sorts s sort-order))
		 (all-subs subs)
		 (same-compo (list s))
		 (sname nil)
		 (found nil)
		 (hidden nil)
		 err-sort)
	    ;; gather tops in the same connected component.
	    ;; if found one, we again must walk through the rest.
	    (loop (setf found nil)
		  (dolist (m (cdr maximal))
		    (let ((msub (sub-or-equal-sorts m sort-order)))
		      (when (intersection all-subs msub :test #'eq)
			(setf all-subs (union all-subs msub :test #'eq))
			(setf found t)
			(push m same-compo))))
		  (setf maximal (set-difference maximal same-compo))
		  (when (or (null maximal) (not found)) (return)))
	    ;;
	    (setq hidden (sort-is-hidden (car same-compo)))
	    (setq sname (make-err-sort-name same-compo))
	    (let ((old (find-the-equivalent-error-sort
			sname
			same-compo
			old-errs)))
	      ;; for debug
	      (when *on-sort-debug*
		(with-output-simple-msg ()
		  (format t "~%[generate-err-sorts]: name = ~a" sname)
		  (format t "~%- predefined : ~a" old)
		  (when old
		    (format t "~% with compo = ~a" (err-sort-components old)))
		  ))
	      ;;
	      (if old
		  ;; use the existing one.
		  (progn
		    (setq err-sort old)
		    (setq old-errs (delete old old-errs :test #'eq)))
		  ;; we need brand new sort.
		  (setq err-sort (define-err-sort sname
				     module
				   same-compo
				   all-subs
				   hidden)))
	      (push err-sort all-errors)
	      (dolist (a all-subs)
		(setf (the-err-sort a sort-order) err-sort)))))
	;; done all.
	(setf (module-error-sorts module) all-errors)
	;; returns obsolete sorts.
	old-errs))))
    
;;; ****************
;;; SORT DECLARATION ___________________________________________________________
;;; ****************

;;; DECLARE-SORT-IN-MODLE : sort-name module -> sort
;;;
(defun declare-sort-in-module (sort-name &optional
					 (module *current-module*)
					 (type 'sort)
					 (hidden nil))
  (let ((mod (if (module-p module)
		 module
		 (find-module-in-env module))))
    (unless mod
      (with-output-chaos-error ('no-such-module)
	(princ "declaring sort, no such module ")
	(print-mod-name module)
	))
    ;;
    (when (or (eq sort-name $name-cosmos)
	      (eq sort-name $name-universal)
	      (eq sort-name $name-huniversal))
      (with-output-chaos-error ('reserved-sort)
	(format t "Sort name ~A is reserfed for the system, sorry."
		sort-name)))
    ;;
    (set-needs-parse module)
    (include-BOOL module)
    ;;
    (let ((sort (define-sort sort-name module type hidden)))
      (add-sort-to-module sort mod)
      sort)))

;;; RECREATE-SORT module sort
;;;
(defun recreate-sort (module sort &optional new-name)
  (let ((sort-name (sort-id sort)))
    (when *on-sort-debug*
      (format t "~&[recreate-sort] : given name ~s, new-name = ~s"
	      sort-name new-name))
    ;;
    (let ((val (find-sort-in module (if new-name new-name sort-name))))
      (if val
	  val
	  (let ((newsort (%copy-sort sort module new-name)))
	    (when *on-sort-debug*
	      (format t "~& - created ~s" (sort-id newsort))
	      (format t " in ")
	      (print-modexp module))
	    newsort
	    )))))

(defun recreate-sorts (module sort-list)
  (mapcar #'(lambda (s) (recreate-sort module s))
	  sort-list))

(defun !recreate-sort (module sort &optional new-name)
  (let ((newsort (%copy-sort sort module new-name)))
    newsort))

(defun !recreate-sorts (module sort-list)
  (mapcar #'(lambda (s) (!recreate-sort module s))
	  sort-list))

;;; SUBSORT DECLARATION ________________________________________________________

;;; DECLARE-SUBSORT-IN-MODULE
;;; order-decls : list of (sort supers)
;;;
(defun declare-subsort-in-module (order-decls &optional (module *current-module*)
					      hidden)
  ;; (declare (optimize (speed 3) (safety 0)))
  (let* ((mod (if (module-p module)
		  module
		  (find-module-in-env module)))
	 (sort-order (if mod (module-sort-order mod)
			 ;; internal error
			 (error "No such module: declare-subsort-in-module ~A" module))))
    (declare (type sort-order sort-order))
    (dolist (decl order-decls)
      (declare (type list decl))
      (declare-subsort-relation decl mod sort-order hidden))
    ;;
    (set-needs-update-sort-order mod)
    (set-needs-parse mod)
    ;;
    sort-order))

;;; relation ::= (sort lower-sorts greater-sorts err-sort)
;;;
(defun adjoin-sort-relation (sl module)
  (let ((s (sort-relation-sort sl))
	(rls (module-sort-relations module)))
    (let ((pre (assq s rls)))
      (if pre
	  (progn (setf (_subsorts pre)
		       (union (_subsorts sl) (_subsorts pre) :test #'eq))
		 (setf (_supersorts pre)
		       (union (_supersorts sl) (_supersorts pre) :test #'eq)))
	  (push sl (module-sort-relations module))))))

#|| BAD THING !!!
(defun clean-up-sort-relations (module)
  (dolist (sl (module-sort-relations module))
    (clean-up-sort-relation sl (module-sort-order module)))
  )

(defun clean-up-sort-relation (sl so)
  (setf (_subsorts sl) (maximal-sorts (_subsorts sl) so))
  (setf (_supersorts sl) (minimal-sorts (_supersorts sl) so)))

||#

;;; declare-subsort-relation
;;;
(defun declare-subsort-relation (order-decl module sort-order &optional hidden)
  (let ((sls (construct-sort-relations order-decl module hidden)))
    (declare (type list sls))
    (when sls
      (dolist (sl sls)
	(adjoin-sort-relation sl module)
	(add-relation-to-order (copy-sort-relation sl) sort-order)))))

;;; CONSTRUCT-SORT-RELATIONS <SubSortDecl>
;;; Returns the list of sort-relations derived from the given
;;; subsort-declaration form.
;;;
(defun construct-sort-relations (order-decl &optional (module *current-module*) hidden)
  (let ((*current-module* module)
	(res nil)
	(tmp nil)
	(work nil))
    (declare (type list res tmp work))
    (dolist (sid order-decl)
      ;; sid can be a list (sort-id module-name)
      (if (eq sid ':<)
	  (progn (push work tmp)
		 (setq work nil))
	  (let ((sort (find-sort-in module sid)))
	    (when (or (eq sort *cosmos*)
		      (eq sort *universal-sort*)
		      (eq sort *huniversal-sort*))
	      (let ((*chaos-quiet* t))
		(with-output-chaos-error ('invalid-sort-relation)
		  (format t "You can not specify the order with built in sort ~A."
			  (string (sort-name sort))))))
	    ;; 
	    (if sort
		(progn
		  (when hidden
		    (unless (sort-is-hidden sort)
		      (with-output-chaos-error ('invalid-subsort-decl)
			(princ "you cannot declare subsort relation between hidden and visible sorts.")
			(print-next)
			(princ "the sort ") (print-sort-name sort)
			(princ " is visible, but must be hidden in this context.")
			)))
		  (push sort work))
		(with-output-chaos-error ('no-such-sort)
		  (princ "constructing sort relation, no such sort with name ")
		  (if (term? sid)
		      (term-print sid)
		      (princ sid))
		  )
		))))
    ;;
    (setq tmp (nreverse (push work tmp)))
    (dotimes (x (length tmp))
      (declare (type fixnum x))
      (dolist (s (nth x tmp))
	(let ((lowers (let ((ls nil))
			(dotimes (y x)
			  (declare (type fixnum y))
			  (setq ls (append ls (nth y tmp))))
			ls))
	      (greaters (do* ((y (1+ x) (1+ y))
			      (res (nth y tmp)
				   (append res (nth y tmp))))
			     ((>= y (the fixnum (length tmp))) res)
			  (declare (type fixnum y)
				   (type list res)))))
	  (declare (type list lowers greaters))
	  ;; check hidden condition
	  (when hidden
	    (when (eq (sort-module s) module)
	      (dolist (ts lowers)
		(unless (eq (sort-module ts) module)
		  (with-output-chaos-warning ()
		    (princ "declaring hidden sort ")
		    (print-sort-name s)
		    (princ " as a supersort of imported hidden sort ")
		    (print-sort-name ts))))))
	  ;;
	  (push (make-sort-relation s lowers greaters) res))))
    res))

;;; UPDATE-SORT-ORDER
;;;  
(defun update-sort-order (module)
  (let ((closure
	 (sort-relations-transitive-closure1 (module-sort-relations module)))
	(so (module-sort-order module)))
    (dolist (sl closure)
      (add-relation-to-order sl so))))

;;; FIND-COMPATIBLE-ERR-SORT (sort module)
;;;
(defun find-compatible-err-sort (sort module &optional sortmap)
  (when (or (sort= sort *cosmos*)
	    (sort= sort *universal-sort*)
	    (sort= sort *bottom-sort*)
	    (sort= sort *huniversal-sort*)
	    )
    (return-from find-compatible-err-sort sort))
  ;;
  (cond ((err-sort-p sort)
	 (or (cdr (memq sort sortmap))
	     (let* ((compo (car (err-sort-components sort)))
		    (xs (if sortmap
			    (modmorph-assoc-image sortmap compo)
			    compo)))
	       ;;
	       (or (the-err-sort xs (module-sort-order module))
		   sort))))
	(t (let ((xs (if sortmap
			 (modmorph-assoc-image sortmap sort)
			 sort)))
	     (the-err-sort xs (module-sort-order module))))))

;;;
;;; SUPPORT FUNCTIONS for SORT MEMBERSHIP PREDICATE.
;;;

(defun method->sort-name (method)
  (let ((name (method-symbol method)))
    (if (cdr name)
	(with-output-chaos-error ('invalid-sort-id)
	  (format t "operator name ~s is illegal for sort name." name))
	(car name))))

(defun get-sort-id-value (id-term)
  (if (term-is-builtin-constant? id-term)
      (term-builtin-value id-term)
      (method->sort-name (term-head id-term))))

(defun gather-sorts-with-id (sort-id-term module)
  (declare (type term sort-id-term))
  (if (term-is-variable? sort-id-term)
      (list (variable-sort sort-id-term))
      (let ((sort-name (get-sort-id-value sort-id-term)))
	(find-all-sorts-in module sort-name))))

;;;
;;; the generic sort membership tester
;;;
(declaim (special .test-term-sort-membership-in-progress.))
(defvar .test-term-sort-membership-in-progress. nil)

(defun test-term-sort-membership (term sort-id-const
				       &optional
				       (module (or *current-module*
						   *last-module*)))
  (declare (type term term sort-id-const))
  (unless module
    (with-output-chaos-error ('no-context)
      (princ "sort membership: no context module is given!")))
  (with-in-module (module)
    (let ((sorts (gather-sorts-with-id sort-id-const module))) 
      (unless sorts
	(with-output-chaos-error ('no-sort)
	  (format t "sort membership: no such sort ~a in the current context."
		  (get-sort-id-value sort-id-const))))
      
      ;; first we compute the sort with considering sort membership
      ;; predicates in recursive manner.
      (unless .test-term-sort-membership-in-progress.
	(let ((.test-term-sort-membership-in-progress. term))
	  (apply-sort-memb term module)))

      ;; test the result.
      (let ((term-sort (term-sort term)))
	(if (some #'(lambda (x)
		      (sort<= term-sort x *current-sort-order*))
		  sorts)
	    t
	    nil))))
  )

;;; SORT-IS-PARAMETERIZED : sort -> Bool
;;; returns t iff sort is of paramter theory module.
;;;
(defun sort-is-parameterized (sort)
  (declare (type sort* sort))
  (module-is-parameter-theory (sort-module sort)))

;;; EOF
