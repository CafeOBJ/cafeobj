;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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

(defstruct (object (:conc-name "OBJECT-")
		   (:constructor make-object)
		   (:constructor object* nil)
		   (:copier nil)
		   (:include %chaos-object (-type 'object))
		   (:print-function chaos-pr-object))
  (misc-info nil :type list)
  (context-mod nil))

(defmacro object-info (_obj _info)
  ` (getf (object-misc-info ,_obj) ,_info))

(defun set-object-context-module (obj &optional (context-mod (get-context-module)))
  (setf (object-context-mod obj) context-mod))

; (eval-when (:execute :load-toplevel)
;   (setf (symbol-function 'is-object)(symbol-function 'object-p))
;   (setf (get 'object ':type-predicate) (symbol-function 'is-object))
;   (setf (get 'object :eval) nil)
;   (setf (get 'object :print) nil))

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

;;; ************
;;; SYMBOL-TABLE
;;; ************
(defstruct (symbol-table)
  (names nil :type list)
  (map (make-hash-table :test #'equal)))

(defstruct (stable)
  (sorts nil :type list)
  (operators nil :type list)
  (parameters nil :type list)
  (submodules nil :type list)
  (variables nil :type list)
  (axioms nil :type list)
  (unknowns nil :type list))

(defun canonicalize-object-name (nm)
  (cond ((stringp nm)
	 (intern nm))
	((consp nm)
	 (if (cdr nm)
	     (mapcar #'canonicalize-object-name nm)
	   (canonicalize-object-name (car nm))))
	((symbolp nm) nm)
	((module-p nm) (canonicalize-object-name (module-name nm)))
	(t
	 ;; do nothing
	 )))

(defun symbol-table-add (table nm obj)
  (when (and (module-p obj)
	     (module-is-parameter-theory obj))
    (setq nm (car (module-name obj))))
  (let ((name (canonicalize-object-name nm)))
    (pushnew name (symbol-table-names table) :test #'equal)
    (let* ((map (symbol-table-map table))
	   (tbl (gethash name map)))
      (unless tbl
	(setf tbl (setf (gethash name map) (make-stable))))
      (cond ((sort-p obj)
	     (pushnew obj (stable-sorts tbl)))
	    ((operator-p obj)
	     (pushnew obj (stable-operators tbl)))
	    ((module-p obj)
	     (if (module-is-parameter-theory obj)
		 (pushnew obj (stable-parameters tbl))
	       (pushnew obj (stable-submodules tbl))))
	    ((axiom-p obj)
	     (pushnew obj (stable-axioms tbl)))
	    ((and (termp obj)
		  (term-is-variable? obj))
	     (pushnew obj (stable-variables tbl)))
	    (t (pushnew obj (stable-unknowns tbl))))
      tbl)))

(defun symbol-table-get (name &optional (module (get-context-module)))
  (let ((gname (canonicalize-object-name name)))
    (gethash gname (symbol-table-map
		    (module-symbol-table module)))))

;;;=============================================================================
;;; TOP-OBJECT _________________________________________________________________
;;; **********

;;; represents common structure of top-level semantic objects.
;;; 
(defstruct (top-object (:conc-name "TOP-OBJECT-")
		       (:constructor make-top-object)
		       (:constructor top-object* (name))
		       (:copier nil)
		       (:include object (-type 'top-object)))
  (name nil)
  (interface (make-ex-interface) :type (or null ex-interface))
  (status -1 :type fixnum)
  (decl-form nil :type list)
  (symbol-table (make-symbol-table) :type symbol-table))

; (eval-when (:execute :load-toplevel)
;   (setf (symbol-function 'is-top-object)(symbol-function 'top-object-p))
;   (setf (get 'top-object ':type-predicate) (symbol-function 'is-top-object))
;   (setf (get 'top-object :eval) nil)
;   (setf (get 'top-object :print) nil))

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
	  (princ "exporting-objects: invalid interface of object ")
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
  (setf (interface$exporting-objects interface) nil))

(defun clean-up-ex-interface (interface)
  (declare (type ex-interface interface)
	   (values t))
  (setf (interface$dag interface) nil)
  (setf (interface$parameters interface) nil)
  (setf (interface$exporting-objects interface) nil))

;;;
;;; setting dependency
;;;
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
  (pushnew (cons object mode) (object-exporting-objects subobject) :test #'equal))

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

;;; *****************
;;; MODULE-PARSE-INFO___________________________________________________________
;;; *****************
;;; constructed one per module. holds syntactical informations on valid tokens.
;;; consists of two slots:
;;;  table : holds token inforations. key is a token (a string), and the value
;;;          is a list of methods whose operator name begins with the token.
;;;          juxtaposition operators are not stored here, they are treated
;;;          specially during parsing process (infos on juxtapos ops are stored
;;;          in module's slot (juxtaposition).
;;;  builtins : list of infos on builtin constants. each info consists of the
;;;             builtin-info part of builtin sorts.
;;;

(defstruct (parse-dictionary (:conc-name "DICTIONARY-"))
  (table (make-hash-table :test #'equal :size 50)
	 :type (or null hash-table))
  (builtins nil :type list)
  (juxtaposition nil :type list)	; list of juxtaposition methods.
  )

;;; *********
;;; SIGNATURE___________________________________________________________________
;;; *********
;;; gathers own signature infomations of a module. stored in module's `signature'
;;; slot.

(defstruct (signature-struct (:conc-name "SIGNATURE$")
	    (:print-function print-signature))
  (module nil)				; module 
  (sorts nil :type list)		; list of own sorts.
  (sort-relations nil :type list)	; list of subsort relations.
  (operators nil :type list)		; list of operators declared in the
					; module. 
  (opattrs nil :type list)		; explicitly declared operator
					; attributes in a form of AST.
  (principal-sort nil :type atom)	; principal sort of the module.
  )

(defun print-signature (obj stream &rest ignore)
  (declare (ignore ignore))
  (let ((mod (signature$module obj)))
    (format stream "'[:signature \"~a\"]" (make-module-print-name2 mod))))

;;; *********
;;; AXIOM-SET___________________________________________________________________
;;; *********
;;; gathers own axioms and explicitly declared variables of a module.
;;; stored in module's `axioms' slot.

(defstruct (axiom-set (:conc-name "AXIOM-SET$")
	    (:print-function print-axiom-set))
  (module nil)				; contaning module
  (variables nil :type list)		; assoc list of explicitly declared
					; variables.  
					;  ((variable-name . variable) ...)
  (equations nil :type list)		; list of equtions declared in the module.
  (rules nil :type list)		; list of rules declared in the module.
  )

(defun print-axiom-set (obj stream &rest ignore)
  (declare (ignore ignore))
  (let ((mod (axiom-set$module obj)))
    (format stream "':axset[\"~a\"]" (module-print-name mod))))

;;; ***
;;; TRS________________________________________________________________________
;;; ***

(let ((.ext-rule-table-symbol-num. 0))
  (declare (type fixnum .ext-rule-table-symbol-num.))
  (defun make-ext-rule-table-name ()
    (declare (values symbol))
    (intern (format nil "ext-rule-table-~d" (incf .ext-rule-table-symbol-num.))))
  )

;;; The structure TRS is a representative of flattened module.

(defstruct (TRS (:conc-name trs$)
	        (:print-function print-trs))
  (module nil :type (or null top-object))	; the reverse pointer
  ;; SIGNATURE INFO
  (opinfo-table	(make-hash-table :test #'eq)
		:type (or null hash-table))
					; operator infos
  (sort-order (make-hash-table :test #'eq)
	      :type (or null hash-table))
					; transitive closure of sort-relations
  ;; (ext-rule-table (make-hash-table :test #'eq))
  (ext-rule-table (make-ext-rule-table-name)
		  :type symbol)
					; assoc table of rule A,AC extensions
  ;;
  (sorts nil :type list)		; list of all sorts
  (operators nil :type list)		; list of all operators
  ;; REWRITE RULES
  (rules nil :type list)		; list of all rewrite rules.
  ;; INFO FOR EXTERNAL INTERFACE -----------------------------------
  (sort-name-map nil :type list)
  (op-info-map nil :type list)
  (op-rev-table nil :type list)
  ;; GENERATED OPS & AXIOMS for equalities & if_then_else_fi
  ;; for proof support system.
  (sort-graph nil :type list)
  (err-sorts nil :type list)
  (dummy-methods nil :type list)
  (sem-relations nil :type list)	; without error sorts
  (sem-axioms nil :type list)		; ditto
  ;; a status TRAM interface generated?
  (tram	nil :type symbol)		; nil,:eq, or :all
  )

(defun print-trs (obj stream &rest ignore)
  (declare (ignore ignore))
  (let ((mod (trs$module obj)))
    (format stream "'[:trs \"~a\"]" (make-module-print-name2 mod))))

;;; ******************
;;; MODULE-DYN-CONTEXT___________________________________________________________
;;; ******************
;;; holds run time dynamic infomation of a module.

(defstruct (module-dyn-context (:conc-name "MODULE-CONTEXT-"))
  (object nil :type (or null object))	; module
  (bindings nil :type list)		; top level let binding
  (special-bindings nil :type list)	; users $$variables ...
  ($$term nil :type list)		; $$term
  ($$subterm nil :type list)		; $$subterm
  ($$action-stack nil :type list)	; action stack for apply
  ($$selection-stack nil :type list)	; selection stack for choose
  ($$stop-pattern nil :type list)	; stop pattern
  ($$ptree nil)				; proof tree
  )

;;;
;;; *********
;;; MODULE    __________________________________________________________________
;;; STRUCTURE
;;; *********
(defstruct (module (:include top-object (-type 'module))
		   (:conc-name "MODULE-")
		   (:constructor make-module)
		   (:constructor module* (name))
		   (:print-function print-module-object))
  (print-name "" :type string)
  (signature nil :type (or null signature-struct))
					; own signature.
  (axiom-set nil :type (or null axiom-set))
					; set of own axioms.
  (theorems nil :type list)		; set of own theorems, not used yet.
  (parse-dictionary nil :type (or null parse-dictionary))
					; infos for term parsing.
  (trs nil :type (or null trs))		; corresponding semi-compiled TRS.
  (context nil
	   :type (or null module-dyn-context))
					; run time context
  (alias nil :type list)		; alias names for a module generated from complex modexpr
  )

;;; KIND
(defmacro module-kind (_mod)
  `(getf (object-misc-info ,_mod) ':module-kind))

(defmacro module-is-theory (_mod_) `(eq :theory (module-kind ,_mod_)))

(defmacro module-is-object (_mod_) `(eq :object (module-kind ,_mod_)))

(defmacro module-is-final (_mod_) `(eq :theory (module-kind ,_mod_)))

(defmacro module-is-loose (_mod_)
  ` (memq (module-kind ,_mod_) '(:module :ots)))

(defmacro module-is-initial (_mod_) `(eq (module-kind ,_mod_) :object))

;;; PRINTER

(defun print-module-object (obj stream &rest ignore)
  (declare (ignore ignore)
	   (type module obj)
	   (type stream stream)
	   (values t))
  (if (or (module-is-inconsistent obj)
	  (null (module-name obj)))
      (format stream ":module[\"~a\"]" (module-name obj))
    (cond ((module-is-object obj)
	   (format stream ":mod![\"~a\"]" (module-print-name obj)))
	  ((module-is-theory obj)
	   (format stream ":mod*[\"~a\"]" (module-print-name obj)))
	  (t (format stream ":mod[\"~a\"]" (module-print-name obj))))))

;;; ****
;;; VIEW _______________________________________________________________________
;;; ****
;;;  - source & target modules are evaluated.
;;;  - sorts "found".
;;;  - terms parsed, operator references are resolved.
;;;  - variables are eliminated.
;;;-----------------------------------------------------------------------------

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
  (format stream ":view[~a: ~s => ~s | ~s]"
	  (view-struct-name obj)
	  (view-struct-src obj)
	  (view-struct-target obj)
	  (addr-of obj)))


;;; EOF
