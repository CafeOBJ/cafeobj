;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
;;; $Id: bobject.lisp,v 1.1.1.1 2003-06-19 08:29:30 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: primitives
			       File: bobject.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; definitions of term structures of semantic objects     -- objects
;;; categorized into :object, and
;;; definitions of some principle internal data structures -- objects
;;; categorized into :int-object.
;;;

;;; *NOTE*
;;; depends on `term.lisp' for `defterm' construct.

;;;=============================================================================
;;; OBJECT/INT-OBJECT___________________________________________________________
;;; *****************
;;; definition of semantic object & internal data structure.
;;; all objects defined in this file inherits either %object or %int-object.

#||
;;; term structure of semantic object of Chaos.
(defterm object () :category ':object) 

(defterm static-object () :category ':static-object)

;;; structure of internal object of Chaos.
(defterm int-object () :category ':int-object)

(defterm static-int-object () :category ':static-int-object)
||#

(defstruct (object (:conc-name "OBJECT-")
		   (:constructor make-object)
		   (:constructor object* nil)
		   (:copier nil)
		   (:include %chaos-object (-type 'object))
		   (:print-function chaos-pr-object)))
(eval-when (eval load)
  (setf (symbol-function 'is-object)(symbol-function 'object-p))
  (setf (get 'object ':type-predicate) (symbol-function 'is-object))
  (setf (get 'object :eval) nil)
  (setf (get 'object :print) nil))

;;;=============================================================================
;;; TOP-OBJECT _________________________________________________________________
;;; **********

;;; represents common structure of top-level semantic objects.
;;; 
#||
(defterm top-object (object)		; was (static-object)
  :visible (name)			; name.
  :hidden (interface			; external interface.
	   status			; object status.
	   decl-form			; declaration form
	   )
  )
||#
(defstruct (top-object (:conc-name "TOP-OBJECT-")
		       (:constructor make-top-object)
		       (:constructor top-object* (name))
		       (:copier nil)
		       (:include object (-type 'top-object)))
  (name nil)
  (interface (make-ex-interface) :type (or null ex-interface))
  (status -1 :type fixnum)
  (decl-form nil :type list))

(eval-when (eval load)
  (setf (symbol-function 'is-top-object)(symbol-function 'top-object-p))
  (setf (get 'top-object ':type-predicate) (symbol-function 'is-top-object))
  (setf (get 'top-object :eval) nil)
  (setf (get 'top-object :print) nil))

;;; *********
;;; INTERFACE
;;; *********
;;; gathers informations for external interface of a top-level objects.

(defstruct (ex-interface (:conc-name "INTERFACE$"))
  (dag nil :type (or null dag-node))	; DAG of dependency hierarchy. 
  (parameters nil :type list)		; list of parmeter modules.
					; (also in dag).
  (exporting-objects nil :type list)	; list of objects depending this one.
					; (object . mode)
					; mode ::= :protecting | :exporting | :using
					;        | :modmorph | :view
  )

;;;
;;; basic accessors via top-object
;;;
(defmacro object-depend-dag (_object)
  `(interface$dag (top-object-interface ,_object)))

(defun object-parameters (_object)
  (declare (type top-object _object)
	   (values list))
  (let ((interf (top-object-interface _object)))
    (if interf
	(interface$parameters interf)
	nil)))

(defsetf object-parameters (_obj) (_value)
  ` (let ((interf (top-object-interface ,_obj)))
      (unless interf
	(with-output-panic-message ()
	  (princ "invalid interface of object ")
	  (print-chaos-object ,_obj)
	  (chaos-error 'panic)))
      (setf (interface$parameters interf) ,_value)))

(defun object-exporting-objects (_object)
  (declare (type top-object _object)
	   (values list))
  (let ((interf (top-object-interface _object)))
    (if interf
	(interface$exporting-objects interf)
	nil)))

(defsetf object-exporting-objects (_object) (_value)
  ` (let ((interf (top-object-interface ,_object)))
      (unless interf
	(with-output-panic-message ()
	  (princ "invalid interface of object ")
	  (print-chaos-object ,_object)
	  (chaos-error 'panic)))
      (setf (interface$exporting-objects interf) ,_value)))
  
(defun object-direct-sub-objects (_object)
  (declare (type top-object _object)
	   (values list))
  (let ((interf (top-object-interface _object)))
    (if interf
	(mapcar #'dag-node-datum
		(dag-node-subnodes (interface$dag interf)))
	nil)))

(defun object-all-sub-objects (object)
  (declare (type top-object object)
	   (values list))
  (when (top-object-interface object)
    (let ((res (cons nil nil)))
      (gather-sub-objects object res)
      (car res))))

(defun gather-sub-objects (object res)
  (declare (type top-object object)
	   (type list res)
	   (values list))
  (let ((dmods (object-direct-sub-objects object)))
    (dolist (dmod dmods)
      (unless (member dmod (car res) :test #'equal)
	(push dmod (car res))
	(gather-sub-objects (car dmod) res)))))

(defun object-all-exporting-objects (object)
  (declare (type top-object object)
	   (values list))
  (when (top-object-interface object)
    (let ((res (cons nil nil)))
      (gather-exporting-objects object res)
      (car res))))

(defun gather-exporting-objects (object res)
  (declare (type top-object object)
	   (type list res)
	   (values list))
  (let ((dmods (object-exporting-objects object)))
    (dolist (dmod dmods)
      (unless (member dmod (car res) :test #'equal)
	(push dmod (car res))
	(gather-exporting-objects (car dmod) res)))))

;;;
;;; initialization
;;;
(defun initialize-depend-dag (object)
  (declare (type top-object object)
	   (values t))
  (let ((dag (object-depend-dag object)))
    (if dag
	(setf (dag-node-subnodes dag) nil)
	(let ((node (create-dag-node (cons object nil) nil)))
	  (setf (object-depend-dag object) node)))))

(defun initialize-object-interface (interface)
  (declare (type ex-interface interface)
	   (values t))
  (setf (interface$parameters interface) nil)
  (setf (interface$exporting-objects interface) nil)
  )

(defun clean-up-ex-interface (interface)
  (declare (type ex-interface interface)
	   (values t))
  (setf (interface$dag interface) nil)
  (setf (interface$parameters interface) nil)
  (setf (interface$exporting-objects interface) nil)
  )

;;;
;;; setting dependency
;;;
#||
(defvar *top-object-depend-dag-table* (make-hash-table :test #'equal))

(defun add-depend-relation (object mode subobject)
  ;; set dag
  (let ((dag (object-depend-dag object)))
    (unless dag
      (setq dag (create-dag-node (cons object nil) nil))
      (setf (object-depend-dag object) dag))
    (let ((sub-dag (object-depend-dag subobject)))
      (unless sub-dag (break "Panic! no module dag of subobject..."))
      (let* ((submod-datum (cons subobject mode))
	     (s-node (or (gethash submod-datum *top-object-depend-dag-table*)
			 (setf (gethash submod-datum *top-object-depend-dag-table*)
			       (create-dag-node submod-datum
						(dag-node-subnodes sub-dag))))))
	(push s-node (dag-node-subnodes dag)))))
  ;; make exporting relation
  (pushnew (cons object mode) (object-exporting-objects subobject) :test #'equal))

||#

(defun add-depend-relation (object mode subobject)
  (declare (type top-object object)
	   (type symbol mode)
	   (type top-object subobject)
	   (values t))
  ;; set dag
  (let ((dag (object-depend-dag object)))
    (unless dag
      (setq dag (create-dag-node (cons object nil) nil))
      (setf (object-depend-dag object) dag))
    (let ((sub-dag (object-depend-dag subobject)))
      (unless sub-dag (break "Panic! no object dag of subobject..."))
      (let* ((submod-datum (cons subobject mode))
	     (s-node (create-dag-node submod-datum
				      (dag-node-subnodes sub-dag))))
	(push s-node (dag-node-subnodes dag)))))
  ;; make exporting relation
  ;; (pushnew (cons object mode) (object-exporting-objects subobject) :test #'equal)
  (pushnew (cons object mode) (object-exporting-objects subobject) :test #'equal)
  )

;;; ******
;;; STATUS
;;; ******

;;; the status is represented by an integer value; 
;;; -1 : initial status.
;;; 0  : inconsistent.
;;; other positive integer values are used and their meanings are depend on
;;; each type of object.
;;;
(defmacro object-status (_object) `(top-object-status ,_object))

(defmacro object-is-inconsistent (_object_) `(= (object-status ,_object_) 0))

(defmacro mark-object-as-inconsistent (_object_)
  `(setf (object-status ,_object_) 0))

;;; change propagation.
;;; mark object as inconsistent.
;;;
(defun propagate-object-change (exporting-objects)
  (declare (type list exporting-objects)
	   (values t))
  (dolist (eobj exporting-objects)
    (mark-object-as-inconsistent (car eobj))
    (propagate-object-change (object-exporting-objects (car eobj)))))

;;; *********
;;; DECL-FORM
;;; *********

;;; object's declaration form in AST.

(defmacro object-decl-form (_object)  `(top-object-decl-form ,_object))

;;;=============================================================================
;;; SCRIPT _____________________________________________________________________
;;; ******
;;: defines the common structure of script language.
(defterm script ()  :category :chaos-script)

(defun script? (obj) (eq (ast-category obj) ':chaos-script))

;;;============================================================================= 
;;; AST ________________________________________________________________________
;;; ***
;;; common structure of abstract syntax.
;;;

(defterm ast () :category :ast)

(defun ast? (obj) (eq (ast-category obj) ':ast))

;;; EOF
