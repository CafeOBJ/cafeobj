;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
;;; $Id: bview2.lisp,v 1.1.1.1 2003-06-19 08:28:59 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: primitives
				File: bview.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************************************************************************
;;; ************* INTERNAL STRUCTURE OF VIEW & BASIC OPERATIONS ****************
;;; ****************************************************************************

;;; ****
;;; VIEW _______________________________________________________________________
;;; ****
;;;  - source & target modules are evaluated.
;;;  - sorts "found".
;;;  - terms parsed, operator references are resolved.
;;;  - variables are eliminated.
;;;-----------------------------------------------------------------------------
#||
(defterm view-struct (top-object)
  :visible (name)			; view name (string).
  :hidden (src				; source module
	   target			; target module
	   sort-maps			; mapping of sorts
	   op-maps			; mapping of operators
	   )
  :print print-view-internal
  :int-printer print-view-struct-object)
||#

#||
(defstruct (view-struct (:include top-object (-type 'view-struct))
			(:conc-name "VIEW-STRUCT-")
			(:constructor make-view-struct)
			(:constructor view-struct* (name))
			(:copier nil)
			(:print-function print-view-struct-object))
  (src nil :type (or null module))
  (target nil :type (or null module))
  (sort-maps nil :type list)
  (op-maps nil :type list))

(eval-when (:execute :load-toplevel)
  (setf (symbol-function 'is-view-struct) (symbol-function 'view-struct-p))
  (setf (get 'view-struct :type-predicate) (symbol-function 'view-struct-p))
  (setf (get 'view-struct :print) 'print-view-internal))

(defun print-view-struct-object (obj stream &rest ignore)
  (declare (ignore ignore))
  (format stream "#<view ~a : ~x>" (view-struct-name obj) (addr-of obj)))

||#

;;; accessors, all are setf'able

(defmacro view-name (_view) `(view-struct-name ,_view))
(defmacro view-src (_view) `(view-struct-src ,_view))
(defmacro view-source (_view) `(view-struct-src ,_view)) ; synonym
(defmacro view-target (_view) `(view-struct-target ,_view))
(defmacro view-sort-maps (_view) `(view-struct-sort-maps ,_view))
(defmacro view-op-maps (_view) `(view-struct-op-maps ,_view))
(defmacro view-decl-form (_view) `(object-decl-form ,_view))
(defmacro view-interface (_view) `(view-struct-interface ,_view))
(defmacro view-exporting-objects (_view) `(object-exporting-objects ,_view))
(defmacro view-status (_view) `(object-status ,_view))

;;; basic predicates

(defun view-p (object)
  (declare (type t object)
	   (values (or null t)))
  (view-struct-p object))

;;; MODEXP-IS-VIEW : object -> Bool
;;;
(defun modexp-is-view (object)
  (declare (type t object)
	   (values (or null t)))
  (or (view-p object) (%is-view object)))


(defun view-is-inconsistent (view)
  (declare (type view-struct view)
	   (values (or null t)))
  (object-is-inconsistent view))

;;; view status
(defun mark-view-as-consistent (view)
  (declare (type view-struct view)
	   (values fixnum))
  (setf (object-status view) 1))

;;; change propagation
;;; NOTE: this is not enough, now defined in module.lisp
;;; (defun propagate-view-change (view)
;;;   (declare (type view-struct view)
;;; 	   (values t))
;;;   (propagate-object-change (view-exporting-objects view)))

;;; copy
(defun copy-view (from to)
  (declare (type view-struct from to)
	   (values t))
  (setf (view-name to) (view-name from)
	(view-decl-form to) (view-decl-form from)
	(view-src to) (view-src from)
	(view-target to) (view-target from)
	(view-sort-maps to) (view-sort-maps from)
	(view-op-maps to) (view-op-maps from)
	(view-interface to) (view-interface from)))

;;; initialization
(defun initialize-view (view)
  (declare (type view-struct view)
	   (values t))
  (setf (view-status view) -1)
  (if (the (or null ex-interface) (view-interface view))
      (initialize-object-interface (view-interface view))
      (setf (view-interface view) (make-ex-interface)))
  (setf (view-src view) nil
	(view-target view) nil
	(view-sort-maps view) nil
	(view-op-maps view) nil
	(view-decl-form view) nil
	))

(defun clean-up-view (view)
  (declare (type view-struct view)
	   (values t))
  (setf (view-name view) nil)
  (setf (view-status view) 0)
  (if (view-interface view)
      (clean-up-ex-interface (view-interface view)))
  (setf (view-interface view) nil)
  (setf (view-src view) nil
	(view-target view) nil
	(view-sort-maps view) nil
	(view-op-maps view) nil
	(view-decl-form view) nil
	))


;;; ADDITIONAL MODULE EXPRESSIONS ______________________________________

;;; *NOTE* these structure are NOT Chaos's AST.

;;; INSTANTIATION
;;; evaluated
;;; module : module object
;;; args   : (arg-name . view-structure)
;;;
(defstruct int-instantiation
  (module nil :type t)
  (args nil :type list)
  )

;;; PLUS
;;; internal form: args are all evaluated -- module objects.
;;; stored as module name.
;;;
(defstruct int-plus
  (args nil :type list))

;;; RENAME
;;; evaluated.
;;;  module = module object
;;;  sort-maps & op-maps are just the same as of MODMORPH structure.
;;;  
(defstruct int-rename
  (module nil :type t)
  (sort-maps nil :type list)
  (op-maps nil :type list))


;;; UTILS \\\\\\\\\\\\\\\\

;;; SAME-TOP-LEVEL : Module-Expression Module-Expression -> Bool
;;; - checks if two module expressions the same assuming that they have
;;;   been canonicalized below the top level.
;;; - cannot expect all parts of module expressions that have been put in
;;;   normal form to be equal.
;;;
(defun module-eq (x y)
  (declare (type t x y)
	   (values (or null t)))
  (or (equal x y)
      (and (module-p x) (module-eq (module-name x) y))
      (and (module-p y) (module-eq x (module-name y)))))

(defmacro same-renamed-module (_r1 _r2) `(outer-equal ,_r1 ,_r2))

(defmacro same-view-mapping (_v1 _v2) `(outer-equal ,_v1 ,_v2))

(defun outer-equal (x y)
  (declare (type t x y)
	   (values (or null t)))
  (cond ((stringp x) (equal x y))
	((atom x) (eq x y))		;note this includes structures and vectors
	((consp x)
	 (cond ((term? x) (eq x y))
	       (t 
		(and (consp y)
		     (do ((xl x (cdr xl))
			  (yl y (cdr yl))
			  (flag t))
			 ((or (when (or (atom xl) (atom yl))
				(setq flag (eq xl yl))
				t)
			      (when (not (outer-equal (car xl) (car yl)))
				(setq flag nil)
				t))
			  flag))))))
        (t nil)))

(defun same-top-level (me1 me2)
  (declare (type t me1 me2)
	   (values (or null t)))
  (or (module-eq me1 me2)
      (if (and (chaos-ast? me1) (chaos-ast? me2))
	  (cond
	    (;; me1 is renaming 
	     (%is-rename me1)
	     (and (%is-rename me2)
		  (module-eq (%rename-module me1) (%rename-module me2))
		  (same-renamed-module (%rename-map me1) (%rename-map me2))))
	    
	    (;; me1 is instantiation
	     (%is-instantiation me1)
	     (and (%is-instantiation me2)
		  (module-eq (%instantiation-module me1)
			     (%instantiation-module me2))
		  (let ((args1 (%instantiation-args me1))
			(args2 (%instantiation-args me2)))
		    (declare (type list args1 args2))
		    (and (= (length args1) (length args2))
			 (every #'eq args1 args2)))))
	    
	    (;; me1 is module sum
	     (%is-plus me1)
	     (and (%is-plus me2)
		  (equal (%plus-args me1) (%plus-args me2))))
	    ;; 
	    ;; view
	    ((or (%is-view me1)
		 (%is-view me2))
	     (and (module-eq (%view-module me1) (%view-module me2))
		  (module-eq (%view-target me1) (%view-target me2))
		  (same-view-mapping (%view-map me1)
				     (%view-map me2))))
	    
	    (t nil))
	  (if (and (view-p me1) (view-p me2))
	      (and (module-eq (view-src me1)
			      (view-src me2))
		   (module-eq (view-target me1)
			      (view-target me2))
		   (same-view-mapping (view-sort-maps me1)
				      (view-sort-maps me2))
		   (same-view-mapping (view-op-maps me1) (view-op-maps me2)))
	      ;;
	      ;; non pure chaos-object
	      ;;
	      (cond ((and (consp me1) (consp me2))
		     (= (length (the cons me1))
			(length (the cons me2)))
		     (every #'eql me1 me2))
		    ((equal me1 me2) t)
		    ((or (and (atom me2) (not (chaos-ast? me2)))
			 (not (listp me1))
			 (not (listp me2))
			 (not (= (length me1) (length me2))))
		     nil)
		    (t nil)
		    )))))

;;; ************
;;; DUMMY MODULE________________________________________________________________
;;; ************

;;; dymmy module is used for delays the identification of module to which mapped
;;; (renamed) sorts or operators belog.

(defmacro get-rename-info (*_*mod) `(getf (object-misc-info ,*_*mod) 'rename-mod))

(defun create-dummy-module (map mod info)
  (declare (type modmorph map)
	   (type module mod)
	   (type t info)
	   (values module))
  (let ((val (assq mod (modmorph-module map))))
    (if val
	(cdr val)
	(let ((newmod (make-module :name "DUMMY")))
	  (initialize-module newmod)
	  (setf (get-rename-info newmod) (cons mod info))
	  newmod))))

(defun create-dummy-module-then-map (map mod info)
  (declare (type modmorph map)
	   (type module mod)
	   (type t info)
	   (values module))
  (let ((dmod (create-dummy-module map mod info)))
    (pushnew (cons mod dmod) (modmorph-module map)
	     :key #'car :test #'eq)
    dmod))

(defun module-is-rename-dummy-for (mod1 mod)
  (declare (type module mod1 mod)
	   (values (or null t)))
  (if (equal "DUMMY" (module-name mod1))
      (let* ((info (get-rename-info mod))
	     (oldmod (car info)))
	(eq oldmod mod))
      ))

(defun is-dummy-module (mod)
  (declare (type t mod)
	   (values (or null t)))
  (and (module-p mod)
       (equal "DUMMY" (module-name mod))))


;;; EOF