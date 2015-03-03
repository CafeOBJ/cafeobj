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
			       File: bmodule.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************************************************************************
;;; MODULE INTERNAL STRUCTURE & BASIC OPERATORS ********************************
;;; ****************************************************************************

;;; * NOTE*___________________________________________________
;;; all of the type declarations are now moved to bobject.lisp
;;;

;;; *********
;;; MODULE    __________________________________________________________________
;;; STRUCTURE
;;; *********
#||
(defterm module (top-object)
  :visible (name)			; module name (modexpr).
  :hidden  (signature			; own signature.
	    axiom-set			; set of own axioms.
	    theorems			; set of own theorems, not used yet.
	    parse-dictionary		; infos for term parsing.
	    ex-info			; various compiled informations.
	    trs				; corresponding semi-compiled TRS.
	    context			; run time context
	    )
  :int-printer print-module-object
  :print print-module-internal)

(defstruct (module (:include top-object (-type 'module))
		   (:conc-name "MODULE-")
		   (:constructor make-module)
		   (:constructor module* (name))
		   (:print-function print-module-object)
		   )
  (signature nil :type (or null signature-struct))
					; own signature.
  (axiom-set nil :type (or null axiom-set))
					; set of own axioms.
  (theorems nil :type list)		; set of own theorems, not used yet.
  (parse-dictionary nil :type (or null parse-dictionary))
					; infos for term parsing.
  (ex-info nil :type list)		; various compiled informations.
  (trs nil :type (or null trs))	; corresponding semi-compiled TRS.
  (context nil
	   :type (or null module-context))
					; run time context
  (alias nil :type list)
  )

(eval-when (:execute :load-toplevel)
  (setf (get 'module :type-predicate) (symbol-function 'module-p))
  (setf (get 'module :eval) nil)
  (setf (get 'module :print) 'print-module-internal)
  )

||#

;;; type predicate

;;; (defmacro module-p (_object) `(is-module ,_object))

;;; module name
;;; name ::= string
;;;        | modexpr
;;;        | ( string "::" module-1 module-2 )
;;; the last case is the name pattern for formal argument modules.
;;; this type of module must be treated specially in various context,
;;; the following predicates provide some ways to check 

(defun module-is-parameter-theory (m)
  (declare (type t m)
	   (values (or null t)))
  (let ((name (if (module-p m)
		  (module-name m)
		  m)))
    (cond ((modexp-is-simple-name name)
	   (modexp-is-parameter-theory name))
	  ((%is-rename name)
	   (module-is-parameter-theory (%rename-module name)))
	  ((int-rename-p name)
	   (module-is-parameter-theory (int-rename-module name)))
	  ((%is-instantiation name)
	   (module-is-parameter-theory (%instantiation-module name)))
	  ((int-instantiation-p name)
	   (module-is-parameter-theory (int-instantiation-module name)))
	  (t nil))))
  
;;; ****************
;;; MODULE-INTERFACE___________________________________________________________
;;; ****************
;;; gathers informations for external interface of a module.
;;; stored in module's `interface' slot.

;;; Basic accessors, all are setf'able

(defmacro module-dag (_mod) `(object-depend-dag ,_mod))

(defmacro module-parameters (_mod) `(object-parameters ,_mod))

(defmacro module-exporting-modules (_mod) `(object-exporting-objects ,_mod))
					   
;;; (defmacro module-decl-form (_mod) `(object-decl-form ,_mod))

;;; ** structure of interface-dag **********************************************

;;; MODULE HIERARCHY DAG _______________________________________________________
;;; ** see comlib/dag.lisp for the DAG structure.
;;; -- dag node  : < dtum List[node] . flag >
;;; -- datum of dag node : (module . mode)
;;;    mode ::= :protecting | :extending | :using | :modmorph
;;; -- the top of DAG is a node with datum (module . nil), 
#||
                          M
                         / \
                       (pr) (ex)
                      /       \
                     M2        M5
                    /   \      /
                  (pr)  (ex) (pr)
                  /       \  /
                 M3        M4


     < (M . nil) ( < (M2 . pr) ( < (M3 . pr ) nil > < (M4 . ex ) #1= nil> ) >
		   < (M5 . ex) ( < (M4 . pr) #1 > ) >
		  ) >

-----------------------------------------------------------------------------||#        
(defmacro module-dag-submodules (module)
  ` (when (module-interface ,module)
      (let ((dag (module-dag ,module)))
	(if dag
	    (dag-node-subnodes (module-dag ,module))
	    nil))))

;;; for downward compatibility
;;;
(defun module-direct-submodules (module)
  (declare (type module module))
  (delete-if #'(lambda (x)
		 (memq (cdr x) '(:modmorph :view)))
	     (the list
	       (mapcar #'dag-node-datum (the list
					  (module-dag-submodules module))))))

(defun module-submodules (module)	; just an abbriviation for downward compat.
  (declare (type module)
	   (values list))
  (delete-if #'(lambda (x)
		 (memq (cdr x) '(:modmorph :view)))
	     (the list (mapcar #'dag-node-datum
			       (the list
				 (module-dag-submodules module))))))

;;; dag intialization
(defun initialize-module-dag (module)
  (declare (type module)
	   (values t))
  (initialize-depend-dag module))

;;; BASIC UTILS for accessing module DAG

;;; GETTING ALL SUBMODULES

(defun module-all-submodules (mod)
  (declare (type module mod)
	   (values list))
  (let ((res (cons nil nil)))
    (gather-submodules mod res)
    (car res) ))

(defun gather-submodules (mod res)
  (declare (type module mod)
	   (type list res)
	   (values list))
  (let ((dmods (module-direct-submodules mod)))
    (dolist (dmod dmods)
      (unless (or (eq (cdr dmod) :modmorph)
		  (member dmod (car res) :test #'equal))
	(push dmod (car res))
	(gather-submodules (car dmod) res)))))

(defun get-module-dependency (mod)
  (let ((res (cons nil nil)))
    (gather-module-dependency mod res)
    (car res)))

(defun gather-module-dependency (mod res)
  (let ((dmods (mapcar #'dag-node-datum
		       (module-dag-submodules mod))))
    (dolist (dmod dmods)
      (unless (member dmod (car res) :test #'equal)
	(push dmod (car res))
	(gather-module-dependency (car dmod) res)))))

;;; Imported modules of a module are organized into the slot `submodules'
;;; in a form of list "(module . mode) ...".
;;; 

;;; GET-REAL-IMPORTING-MODE module2 module1 -> mode
;;;
(defun get-importing-path (module2 module)
  (declare (type module module2 module)
	   (values list))
  (let ((subs (module-direct-submodules module)))
    (let ((im (assq module2 subs)))
      (if im
	  (list im)
	  (dolist (s subs)
	    (let ((path (list s)))
	      (let ((im2 (get-importing-path module2 (car s))))
		(if im2
		    (return-from get-importing-path
		      (nconc path im2))))))))))

(defun get-real-importing-mode (module2 &optional (module (or *current-module*
							      *last-module*)))
  (declare (type module module2 module)
	   (values symbol))
  ;;
  (let ((path (get-importing-path module2 module)))
    (let ((mode nil))
      (dolist (e path mode)
	(if (null mode)
	    (setq mode (cdr e))
	    (if (eq (car e) module2)
		(return-from get-real-importing-mode
		  (case mode
		    (:protecting (cdr e))
		    (:extending (case (cdr e)
				  (:protecting :?extending)
				  (otherwise (cdr e))))
		    (otherwise (cdr e))))
		(case mode
		  (:protecting (setq mode (cdr e)))
		  (:extending (unless (eq :protecting (cdr e))
				(setq mode (cdr e))))
		  (otherwise (setq mode (cdr e))))))))))

;;; does module1 extend module2 ?
;;;
(defmacro module-extends (_module1_ _module2_)
  `(eq :extending (get-real-importing-mode ,_module2_ ,_module1_)))

;;; does module1 protect module2 ?
;;;
(defmacro module-protects (_module1_ _module2_)
  `(eq :protecting (get-real-importing-mode ,_module2_ ,_module1_)))

;;; does modules1 using module2?
;;;
(defmacro module-using (_module1_ _module2_)
  `(eq :using (get-real-importing-mode ,_module2_ ,_module1_)))

;;; does module1 including module2?
;;;
(defmacro module-including (_module1_ _module2_)
  `(eq :including (get-real-importing-mode ,_module2_ ,_module1_)))
    
;;; reuturns the list of modules imported into the module `module'
(defmacro imported-modules (_module_)
  `(mapcar #'car (module-submodules ,_module_)))

;;; ADD-IMPORTED-MODULE : module mode submodule -> void
;;; moved the real definition below;
;;; (for downward comatibility.)
;;; the real work is setting dependency relations between top level objects,
;;; should use `add-depend-relation' directly...
;;; 
;;; (defun add-imported-module (module mode submodule)
;;;  (setf (module-all-submodules-list module) nil) ; clear cache
;;;  (add-depend-relation module mode submodule))

;;; ** PARAMETERS **************************************************************
;;; each element of module-parameters has the form:
;;;  ((arg-name .  theory-module) . mode)
;;;
;;; We treat submodules without bound parameters as parameters.
;;;
(defmacro parameter-arg-name (_param) `(caar ,_param))

(defmacro parameter-theory-module (_param) `(cdar ,_param))

(defmacro parameter-imported-mode (_param) `(cdr ,_param))

(defmacro parameter-context (_param_)
  `(fourth (module-name (parameter-theory-module ,_param_))))

;;; imported parameterized module(`theory-module' above) has a name of the form:
;;; 
;;;    (arg-name real-module theory-submodule  context-module)
;;;
;;; parameter theory has a name of the form :
;;;   (argname "::" theory-module context-module)
;;;
;;; (defmacro parameter-theory-arg-name (_mod_) `(car (module-name ,_mod_)))
(defun parameter-theory-arg-name (mod)
  (cond ((module-p mod)
	 (let ((name (module-name mod)))
	   (cond ((%is-rename name)
		  (parameter-theory-arg-name (%rename-module name)))
		 ((int-rename-p name)
		  (parameter-theory-arg-name (int-rename-module name)))
		 ((%is-instantiation name)
		  (parameter-theory-arg-name (%instantiation-module name)))
		 ((int-instantiation-p name)
		  (parameter-theory-arg-name (int-instantiation-module name)))
		 (t (parameter-theory-arg-name (module-name mod))))))
	((modexp-is-parameter-theory mod)
	 (car mod))
	(t (with-output-panic-message ()
	     (format t "expecting arg name, given invalid object: ~s" mod)))))

(defun parameter-module-theory (mod)
  (cond ((module-p mod)
	 (let ((name (module-name mod)))
	   (cond ((%is-rename name)
		  (parameter-module-theory (%rename-module name)))
		 ((int-rename-p name)
		  (parameter-module-theory (int-rename-module name)))
		 ((%is-instantiation name)
		  (parameter-module-theory (%instantiation-module name)))
		 ((int-instantiation-p name)
		  (parameter-module-theory (int-instantiation-module name)))
		 (t (parameter-module-theory (module-name mod))))))
	((modexp-is-parameter-theory mod)
	 (third mod))
	(t (with-output-panic-message ()
	     (format t "expecting theory, given invalid object: ~s" mod)))))

(defun parameter-module-context (mod)
  (cond ((module-p mod)
	 (let ((name (module-name mod)))
	   (cond ((%is-rename name)
		  (parameter-module-context (%rename-module name)))
		 ((int-rename-p name)
		  (parameter-module-context (int-rename-module name)))
		 ((%is-instantiation name)
		  (parameter-module-context (%instantiation-module name)))
		 ((int-instantiation-p name)
		  (parameter-module-context (int-instantiation-module name)))
		 (t (parameter-module-context (module-name mod))))))
	((modexp-is-parameter-theory mod)
	 (fourth mod))
	(t (with-output-panic-message ()
	     (format t "expecting parameter context, given invalid object: ~s" mod)))))

;;; ** EXPORTING MODULES *******************************************************

(defun module-direct-exporting-modules (mod)
  (declare (type module mod)
	   (values list))
  (module-exporting-modules mod))

(defun module-all-exporting-modules (mod)
  (declare (type module mod)
	   (values list))
  (let ((res (cons nil nil)))
    (gather-exporting-modules mod res)
    (delete-duplicates (car res) :test #'equal)))

(defun gather-exporting-modules (mod res)
  (declare (type module mod)
	   (type list res)
	   (values list))
  (let ((dmods (module-exporting-modules mod)))
    (dolist (dmod dmods)
      (unless (member dmod (car res) :test #'eq :key #'car)
	(push dmod (car res))
	(gather-exporting-modules (car dmod) res)))))

;;; ** INTERFACE INITIALIZATIONS **********************************************
;;;
(defun initialize-module-interface (module)
  (declare (type module module)
	   (values t))
  (initialize-object-interface (module-interface module)))

;;; *********
;;; SIGNATURE___________________________________________________________________
;;; *********
;;; gathers own signature infomations of a module. stored in module's `signature'
;;; slot.

#||
(defstruct (signature-struct (:conc-name "SIGNATURE$")
			     ;; #+gcl (:static t)
			     )
  (sorts nil :type list)		; list of own sorts.
  (sort-relations nil :type list)	; list of subsort relations.
  (operators nil :type list)		; list of operators declared in the
					; module. 
  (opattrs nil :type list)		; explicitly declared operator
					; attributes in a form of AST.
  (principal-sort nil :type atom)	; principal sort of the module.
  )

||#

;;; accessors via module, all are setf'able.

(defmacro module-sorts (_mod) `(signature$sorts (module-signature ,_mod)))
(defmacro module-own-sorts (_mod)
  `(signature$sorts (module-signature ,_mod)))

(defmacro module-sort-relations (_mod) `(signature$sort-relations
					 (module-signature ,_mod)))
(defmacro module-operators (_mod) `(signature$operators (module-signature
							 ,_mod))) 

(defmacro module-opattrs (_mod) `(signature$opattrs (module-signature ,_mod)))
(defmacro module-principal-sort (_mod) `(signature$principal-sort
					 (module-signature ,_mod)))

;;; intialization
(defun initialize-signature (sig)
  (declare (type signature-struct sig)
	   (values t))
  (setf (signature$sorts sig) nil
	(signature$sort-relations sig) nil
	(signature$operators sig) nil
	(signature$opattrs sig) nil
	(signature$principal-sort sig) nil))

(defun clean-up-signature (sig)
  (initialize-signature sig))

;;; *********
;;; AXIOM-SET___________________________________________________________________
;;; *********
;;; gathers own axioms and explicitly declared variables of a module.
;;; stored in module's `axioms' slot.

#||
(defstruct (axiom-set (:conc-name "AXIOM-SET$")
		      ;; #+gcl (:static t)
		      )
  (variables nil :type list)		; assoc list of explicitly declared
					; variables.  
					;  ((variable-name . variable) ...)
  (equations nil :type list)		; list of equtions declared in the module.
  (rules nil :type list)		; list of rules declared in the module.
  )

||#

;;; accessors from module object, all are setf'able.

(defmacro module-variables (_mod) `(axiom-set$variables (module-axiom-set
							 ,_mod))) 
(defmacro module-equations (_mod) `(axiom-set$equations (module-axiom-set
							 ,_mod)))
(defmacro module-rules (_mod) `(axiom-set$rules (module-axiom-set ,_mod)))

;;; intialization

(defun initialize-axiom-set (axset)
  (declare (type axiom-set axset)
	   (values t))
  (setf (axiom-set$variables axset) nil
	(axiom-set$equations axset) nil
	(axiom-set$rules axset) nil))

(defun clean-up-axiom-set (axset)
  (declare (type axiom-set axset)
	   (values t))
  (initialize-axiom-set axset))

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

#||
(defstruct (parse-dictionary (:conc-name "DICTIONARY-")
			     ;; #+gcl (:static t)
			     )
  (table (make-hash-table :test #'equal :size 50)
	 :type (or null hash-table))
  (builtins nil :type list)
  (juxtaposition nil :type list)	; list of juxtaposition methods.
  )
||#

;;; accessors via module, all are setf'able

(defmacro module-dictionary-table (_mod) `(dictionary-table
					   (module-parse-dictionary 
					    ,_mod)))
(defmacro module-dictionary-builtins (_mod) `(dictionary-builtins
					      (module-parse-dictionary ,_mod))) 
(defmacro module-juxtaposition (_mod) `(dictionary-juxtaposition
					(module-parse-dictionary ,_mod)))

;;; clear-parse-dict : Dictionary -> Dictionary
;;;
(defun clear-parse-dict (dict)
  (declare (type parse-dictionary dict)
	   (values parse-dictionary))
  (clrhash (dictionary-table dict))
  (setf (dictionary-builtins dict) nil
	(dictionary-juxtaposition dict) nil)
  dict)

;;; initialization
(defun initialize-parse-dictionary (pd)
  (declare (type parse-dictionary pd)
	   (values t))
  (if (dictionary-table pd)
      (clrhash (dictionary-table pd)))
  (setf (dictionary-builtins pd) nil
	(dictionary-juxtaposition pd) nil))

(defun clean-up-parse-dictionary (dict)
  (declare (type parse-dictionary dict)
	   (values t))
  (initialize-parse-dictionary dict)
  (setf (dictionary-table dict) nil))

;;; ***
;;; TRS________________________________________________________________________
;;; ***

#||
(let ((.ext-rule-table-symbol-num. 0))
  (declare (type fixnum .ext-rule-table-symbol-num.))
  (defun make-ext-rule-table-name ()
    (declare (values symbol))
    (intern (format nil "ext-rule-table-~d" (incf .ext-rule-table-symbol-num.))))
  )

;;; The structure TRS is a representative of flattened module.

(defstruct (TRS (:conc-name trs$)
		;; #+gcl (:static t)
		)
  (module nil :type (or null module))	; the reverse pointer
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

||#

;;; accessor via module, all are setf'able.
(defmacro module-rewrite-rules (_mod) `(trs$rules (module-trs ,_mod)))
(defmacro module-all-rules (_mod) `(trs$rules (module-trs ,_mod))) ; synonym

(defmacro module-all-sorts (_mod_) `(trs$sorts (module-trs ,_mod_)))
(defmacro module-all-operators (_mod_) `(trs$operators
					 (module-trs ,_mod_)))
(defmacro module-sort-order (_mod_) `(trs$sort-order
				      (module-trs ,_mod_)))
(defmacro module-opinfo-table (_mod_) `(trs$opinfo-table
					(module-trs ,_mod_)))

(defmacro module-ext-rule-table (_mod_)
  `(trs$ext-rule-table (module-trs ,_mod_)))

(defmacro module-trs-sort-name-map (mod)
  `(trs$sort-name-map (module-trs ,mod)))
(defmacro module-trs-op-info-map (mod)
  `(trs$op-info-map (module-trs ,mod)))
(defmacro module-trs-op-rev-table (mod)
  `(trs$op-rev-table (module-trs ,mod)))
(defmacro module-trs-sort-graph (mod)
  `(trs$sort-graph (module-trs ,mod)))
(defmacro module-trs-err-sorts (mod)
  `(trs$err-sorts (module-trs ,mod)))
(defmacro module-trs-dummy-methods (mod)
  `(trs$dummy-methods (module-trs ,mod)))
(defmacro module-trs-sem-relations (mod)
  `(trs$sem-relations (module-trs ,mod)))
(defmacro module-trs-sem-axioms (mod)
  `(trs$sem-axioms (module-trs ,mod)))
(defmacro module-trs-tram (mod)
  `(trs$tram (module-trs ,mod)))

;;; initialization
(defun initialize-trs-ext-interface (trs)
  (declare (type trs trs)
	   (values t))
  (setf (trs$sort-name-map trs) nil
	(trs$op-info-map trs) nil
	(trs$op-rev-table trs) nil
	(trs$sort-graph trs) nil
	(trs$err-sorts trs) nil
	(trs$dummy-methods trs) nil
	(trs$sem-relations trs) nil
	(trs$sem-axioms trs) nil
	(trs$tram trs) nil)
  )

(defun initialize-trs (trs mod)
  (declare (type trs trs)
	   (type module mod)
	   (values t))
  (setf (trs$module trs) mod)
  (setf (trs$sorts trs) nil
	(trs$operators trs) nil
	(trs$rules trs) nil)
  (initialize-trs-ext-interface trs)
  (if (the (or null hash-table) (trs$sort-order trs))
      (clrhash (trs$sort-order trs))
      (setf (trs$sort-order trs)
	    (make-hash-table :test #'eq)))
  (if (the (or null hash-table) (trs$opinfo-table trs))
      (clrhash (trs$opinfo-table trs))
      (setf (trs$opinfo-table trs)
	    (make-hash-table :test #'eq)))
  #||
  (if (trs$ext-rule-table trs)
      (clrhash (trs$ext-rule-table trs))
      (setf (trs$ext-rule-table trs)
	    (make-hash-table :test #'eq)))
  ||#
  (if (trs$ext-rule-table trs)
      (setf (get (trs$ext-rule-table trs) :ext-rules)
	    nil)
      (setf (trs$ext-rule-table trs)
	    (make-ext-rule-table-name)))
  )

(defun clean-up-trs (trs)
  (declare (type trs trs)
	   (values t))
  (setf (trs$module trs) nil)
  (setf (trs$sorts trs) nil
	(trs$operators trs) nil
	(trs$rules trs) nil)
  (initialize-trs-ext-interface trs)
  (if (trs$sort-order trs)
      (clrhash (trs$sort-order trs)))
  (setf (trs$sort-order trs) nil)
  (if (trs$opinfo-table trs)
      (clrhash (trs$opinfo-table trs)))
  (setf (trs$opinfo-table trs) nil)
  #||
  (if (trs$ext-rule-table trs)
      (clrhash (trs$ext-rule-table trs)))
  ||#
  (setf (get (trs$ext-rule-table trs) :ext-rules) nil)
  )

;;; *******
;;; CONTEXT_____________________________________________________________________
;;; *******
;;; holds some run time context infos.

#||
(defstruct (module-context
	     ;; #+gcl (:static t)
	     )
  (bindings nil :type list)		; top level let binding
  (special-bindings nil :type list)	; users $$variables ...
  ($$term nil :type list)		; $$term
  ($$subterm nil :type list)		; $$subterm
  ($$action-stack nil :type list)	; action stack for apply
  ($$selection-stack nil :type list)	; selection stack for choose
  ($$stop-pattern nil :type list)	; stop pattern
  )
||#

;;; accessors via module, all are setf'able.

(defmacro module-bindings (_mod) `(module-context-bindings (module-context
							    ,_mod)))
(defmacro module-special-bindings (_mod) `(module-context-bindings
					   (module-context ,_mod)))
(defmacro module-$$term (_mod) `(module-context-$$term (module-context ,_mod)))
(defmacro module-$$subterm (_mod) `(module-context-$$subterm (module-context
							      ,_mod)))
(defmacro module-$$action-stack (_mod) `(module-context-$$action-stack
					 (module-context ,_mod)))
(defmacro module-$$selection-stack (_mod) `(module-context-$$selection-stack
					    (module-context ,_mod)))

;;; intialization
(defun initialize-module-context (context)
  (declare (type module-context context)
	   (values t))
  (setf (module-context-bindings context) nil
	(module-context-special-bindings context) nil
	(module-context-$$term context) nil
	(module-context-$$subterm context) nil
	(module-context-$$action-stack context) nil
	(module-context-$$selection-stack context) nil
	(module-context-$$ptree context) nil)
  )

(defun clean-up-context (context)
  (declare (type module-context context)
	   (values t))
  (initialize-module-context context))

;;; **************
;;; MODULE-EX-INFO_____________________________________________________________
;;; **************
;;; holds various infos compiled from interface, signature, axioms,etc.
;;; need not a structure, just plist.

;;; INFO general accessors via module, all are setf'able ------------------------
;;; THE FOLLOWINGS ARE SET in SLOT EX-INFO **************************************
;;;  
;;;  protected-modules                  ; list of modules imported as :protecting
;;;  module-type                        ; one of :hard, :user, :system
;;;  module-kind                        ; one of :theory, :object, :module
;;;  void-sorts				; list of sorts with no constructor.
;;;  void-methods			; list of methods with some arity
;;;					; contains void sort.
;;;  sorts-for-regularity		; list of sorts generated to make the
;;;					; module's signature regular.
;;;  methods-for-regularity		; list of methods generated to make the
;;;					; module's signaure regular.
;;;
;;;  methods-with-rwl-axiom nil		; methods for which the congruence
;;;					; relation w.r.t ==> is already generated.
;;;  rules-with-rwl-axiom nil		; rules for which the congruence
;;;					; relation w.r.t ==> is already generated.
;;;  beh-attributes nil			; list of operator method which is attribute
;;;  beh-methods nil			; list of operator method which is method
;;;  methods-with-beh-axiom nil
;;;  beh-axioms-prooved nil		;
;;;  psort-decl                         ; declaration form of principal sort
;;;  error-op-decl                      ; declaration forms of explicit error
;;;                                     ; operators. may contain illegual ones.
;;;  macros
;;;
(defun module-infos (mod) (object-misc-info mod))
(defsetf module-infos (mod) (values)
  `(setf (object-misc-info ,mod) ,values))

;;; PROTECTED MODULES
(defmacro module-protected-modules (_mod)
  ` (getf (object-misc-info ,_mod) ':protected-modules))

;;; TYPE
(defmacro module-type (_mod)
  `(getf (object-misc-info ,_mod) ':module-type))
					
(defmacro module-is-hard-wired (_mod_)
  `(eq :hard (module-type ,_mod_)))

(defmacro module-is-system-module (_mod_)
  `(eq :system (module-type ,_mod_)))

(defmacro module-is-user-module (_mod_)
  ` (let ((type (module-type ,_mod_)))
      (or (eq type :user) (null type))))

;;; HIDDEN
(defmacro module-hidden (_mod)
  ` (getf (object-misc-info ,_mod) ':module-hidden))

;;; KIND
(defmacro module-kind (_mod)
  `(getf (object-misc-info ,_mod) ':module-kind))

(defmacro module-is-theory (_mod_) `(eq :theory (module-kind ,_mod_)))

(defmacro module-is-object (_mod_) `(eq :object (module-kind ,_mod_)))

(defmacro module-is-final (_mod_) `(eq :theory (module-kind ,_mod_)))

(defmacro module-is-loose (_mod_)
  ` (memq (module-kind ,_mod_) '(:module :ots)))

(defmacro module-is-initial (_mod_) `(eq (module-kind ,_mod_) :object))

;;; REGULARITY
(defmacro module-is-regular (_mod)
  `(getf (object-misc-info ,_mod) ':modle-is-regular))

;;; ALL-SUBMODULES-LIST -- cached data
;;; OBSOLETE
;;; (defun module-all-submodules-list (mod)
;;;   (or (object-misc-info-all-submodules-list (object-misc-info mod))
;;;       (setf (object-misc-info-all-submodules-list (object-misc-info mod))
;;;	    (mapcar #'car (module-all-submodules mod)))))

;;; ADD-IMPORTED-MODULE : module mode submodule [alias] -> void
;;; (for downward comatibility.)
;;; the real work is setting dependency relations between top level objects,
;;; should use `add-depend-relation' directly...
;;; 
(defun add-module-alias (module submod alias)
  (when (rassoc alias (module-alias module) :test #'equal)
    (with-output-chaos-error ('invalid-alias)
      (format t "Alias name ~A is already used for module ~A."
	      alias
	      (get-module-print-name submod))))
  (push (cons submod alias) (module-alias module)))

(defun add-imported-module (module mode submodule &optional alias)
  (declare (type module module submodule)
	   (type symbol mode)
	   (values t))
  ;; (setf (module-ex-info-all-submodules-list (object-misc-info module)) nil)
  (when alias
    (add-module-alias module submodule alias))
  (add-depend-relation module mode submodule))

;;; MODULE-INCUDES-RWL
;;;
(defun module-includes-rwl (mod)
  (declare (type module mod)
	   (type (or null t)))
  (assq *rwl-module* (module-all-submodules mod)))


;;; INFOS generated by REGULARIZING PROC.
;;; *************************************

;;; VOID-SORTS
(defmacro module-void-sorts (_mod)
  `(getf (object-misc-info ,_mod) ':void-sorts))

;;; VOID-METHODS
(defmacro module-void-methods (_mod)
  `(getf (object-misc-info ,_mod) ':void-methods))

;;; SORTS-FOR-REGULARITY
(defmacro module-sorts-for-regularity (_mod)
  `(getf (object-misc-info ,_mod) ':sorts-for-regularity))

;;; METHODS-FOR-REGULARITY
(defmacro module-methods-for-regularity (_mod)
  `(getf (object-misc-info ,_mod) ':methods-for-regularity))

;;; BEHAVIOURAL?
;;; *************

;;; MODULE-HAS-BEHAVIOURAL-AXIOMS
;;;
(defmacro module-has-behavioural-axioms (_mod)
  `(getf (object-misc-info ,_mod) ':has-behavioural-axioms))


;;; MODULE-MACROS
;;;
(defmacro module-macros (_mod)
  `(getf (object-misc-info ,_mod) ':macros))

;;; MODULE-SKOLEMS
;;;
(defmacro module-skolem-functions (_mod)
  `(getf (object-misc-info ,_mod) ':skolem-functions))

;;; INSTANCE-DB
;;; ***********
;;; instance db stores all the instances of class sort.
;;; made for persistent object
;;; we store term-body of an instance in the instance db.
;;; retrieving the instance always creates new term.
;;; this is for avoiding destructive replacement of term body.

;;; !!! NEEDS OPTIMIZATION, creates only if it has OBJECT in submodule.
;;; !!! an answer creates on demand. to do.

(defmacro module-instance-db (mod)
  `(getf (object-misc-info ,mod) ':instance-db))

(defun initialize-module-instance-db (mod)
  (declare (type module mod)
	   (values t))
  (let ((db (module-instance-db mod)))
    (if db
	(clrhash db)
	(setf (module-instance-db mod) (make-hash-table :test #'equal)))))

(defun clear-module-instance-db (mod)
  (declare (type module mod)
	   (values t))
  (let ((db (module-instance-db mod)))
    (declare (type (or null hash-table) db))
    (if db (clrhash db))))

;;; MODULE PROTECTED MODE
;;; **********************

(defmacro module-protected-mode (mod)
  `(getf (object-misc-info ,mod) ':protected-mode))

(defmacro module-is-write-protected (mod) ; synonym
  `(getf (object-misc-info ,mod) ':protected-mode))

;;; MODULE CREATION DATE
;;; ********************

(defmacro module-creation-date (mod)
  `(getf (object-misc-info ,mod) ':creation-date))

;;; MODULE RULES/TERMS TO BE FIXED
;;; ******************************

(defmacro module-axioms-to-be-fixed (mod)
  `(getf (object-misc-info ,mod) ':axioms-to-be-fixed))

(defmacro module-terms-to-be-fixed (mod)
  `(getf (object-misc-info ,mod) ':terms-to-be-fixed))

;;; METHODS-WITH-RWL-AXIOM
;;; **********************
(defmacro module-methods-with-rwl-axiom (_mod)
  `(getf (object-misc-info ,_mod) ':methods-with-rwl-axiom))

;;; RULES-WITH-RWL-AXIOM
;;; ********************
(defmacro module-rules-with-rwl-axiom (_mod)
  `(getf (object-misc-info ,_mod) ':rules-with-rwl-axiom))

;;; BEH-STUFF
;;; *********
;;;     ((hsort methods attributes) ....)
;;;
(defmacro module-beh-stuff (_mod)
  `(getf (object-misc-info ,_mod) ':beh-stuff))

;;; BEH-ATTRIBUTES
;;; **************
(defmacro module-beh-attributes (_mod)
  `(getf (object-misc-info ,_mod) ':beh-attributes))

;;; BEH-METHODS
;;; ************
(defmacro module-beh-methods (_mod)
  `(getf (object-misc-info ,_mod) ':beh-methods))

;;; NON-BEH-METHODS
;;; ***************
(defmacro module-non-beh-methods (_mod)
  `(getf (object-misc-info ,_mod) ':non-beh-methods))

;;; NON-BEH-ATTRIBUTES
;;; ******************
(defmacro module-non-beh-attributes (_mod)
  `(getf (object-misc-info ,_mod) ':non-beh-attributes))

;;; COBASIS
;;; *******
(defmacro module-cobasis (_mod)
  `(getf (object-misc-info ,_mod) ':cobasis))

;;; METHODS-WITH-BEH-AXIOM
;;; **********************
(defmacro module-methods-with-beh-axiom (_mod)
  `(getf (object-misc-info ,_mod) ':methods-with-beh-axiom))

;;; BEH-TO-BE-PROVED
;;; ******************
; (defmacro module-beh-to-be-proved (_mod)
;  `(getf (object-misc-info ,_mod) ':beh-to-be-proved))

;;; SOME LITTLE UTILS ********

(defmacro sort-is-for-regularity? (_s &optional _mod)
  (once-only (_s _mod)
    (if _mod
	` (and (eq (sort-module ,_s) ,_mod)
	       (member ,_s (module-sorts-for-regularity ,_mod) :test #'eq))
	` (member ,_s (module-sorts-for-regularity (sort-module ,_s)) :test #'eq))))

(defmacro method-is-for-regularity? (_m &optional _mod)
  (once-only (_m _mod)
    (if _mod
	` (and (eq (method-module ,_m) ,_mod)
	       (member ,_m (module-methods-for-regularity ,_mod) :test #'eq))
	` (member ,_m (module-methods-for-regularity (method-module ,_m))
		  :test #'eq))))

;;; PRINCIPAL SORT DECLARATION _________________________________________________

(defmacro module-psort-declaration (_mod)
  `(getf (object-misc-info ,_mod) ':psort-decl))

;;; ERROR OPERATOR DECLARATIONS ________________________________________________

(defmacro module-error-op-decl (_mod)
  `(getf (object-misc-info ,_mod) ':error-op-decl))

;;; ERROR-SORTS ________________________________________________________________
(defmacro module-error-sorts (_mod)
  `(getf (object-misc-info ,_mod) ':error-sorts))

;;; ERROR-METHODS ______________________________________________________________
(defmacro module-error-methods (_mod)
  `(getf (object-misc-info ,_mod) ':error-methods))

;;; VARIABLE DECLARATIONS (of ERROR SORTS) _____________________________________
(defmacro module-error-var-decl (_mod)
  `(getf (object-misc-info ,_mod) ':error-var-decl))

;;;-----------------------------------------------------------------------------
;;; OTHER misc. infos stored in 'info slots

(defun needs-update-sort-order (mod)
  (getf (object-misc-info mod) ':need-update-sort-order))
(defun set-needs-update-sort-order (mod)
  (setf (getf (object-misc-info mod) ':need-update-sort-order) t))
(defun unset-needs-update-sort-order (mod)
  (setf (getf (object-misc-info mod) ':need-update-sort-order) nil))

(defmacro module-ambig-sorts (_m) `(getf (object-misc-info ,_m) ':ambig-sorts))
(defmacro module-ambig-ops (_m) `(getf (object-misc-info ,_m) ':ambig-ops))

;;; EX-INFO INITIALIZATION -----------------------------------------------------
;;; OBSOLETE

#||
(defun initialize-module-ex-info (ex-info)
  (setf (module-ex-info-protected-modules ex-info) nil
	(module-ex-info-hard-wired ex-info) nil
	(module-ex-info-kind ex-info) nil
	(module-ex-info-all-submodules-list ex-info) nil
	(module-ex-info-infos ex-info) nil))

(defun clean-up-ex-info (ex-info)
  (initialize-module-ex-info ex-info))

||#

;;; *************
;;; Module status_______________________________________________________________
;;; *************

;;; -1: initial value
;;; 0 : inconsistent
;;; 1 : regularized -- NOT USED.
;;; 2 : prepared for parsing
;;; 3 : prepared for rewriting
;;;
;;; o Adding new sort or operator declarations makes the module status to 0.
;;; o Adding new rule makes the module status to at most 2.
;;; o Some changes in any submodule makes the status to 0.
;;;   (should be more fine grained checking for statu change).
;;; 
;;; (defmacro module-status (_mod) `(object-status ,_mod))

;;; initial inconsistent status

(defmacro module-is-inconsistent (_module)
  `(object-is-inconsistent ,_module))

(defun mark-module-as-inconsistent (_module)
  (mark-object-as-inconsistent _module))

;;; parsing preparation

(defmacro need-parsing-preparation (_module)
  `(< (module-status ,_module) 2))

(defmacro module-is-ready-for-parsing (_module)
  `(>= (module-status ,_module) 2))

(defmacro mark-module-ready-for-parsing (_module)
  `(setf (module-status ,_module) (max 2 (module-status ,_module))))

(defmacro mark-need-parsing-preparation (_module)
  `(setf (module-status ,_module) (min 1 (module-status ,_module))))

;;; rewriting preparation

(defmacro need-rewriting-preparation (_module)
  `(< (module-status ,_module) 3))
      
(defmacro module-is-ready-for-rewriting (_module)
  `(>= (module-status ,_module) 3))

(defmacro mark-module-as-consistent (_module)
  `(setf (module-status ,_module) 3))

(defmacro mark-module-ready-for-rewriting (_module)
  `(mark-module-as-consistent ,_module))

(defmacro mark-module-need-rewriting-preparation (_module)
  `(setf (module-status ,_module) (min 2 (module-status ,_module))))

;;; some handy procs.

(defmacro set-needs-parse (&optional (_module '*current-module*))
  `(mark-need-parsing-preparation ,_module))
(defmacro needs-parse (&optional (_module '*current-module*))
  `(prepare-for-parsing ,_module))
(defmacro set-needs-rule (&optional (_module '*current-module*))
  `(mark-module-need-rewriting-preparation ,_module))
(defmacro needs-rule (&optional (_module '*current-module*))
  `(compile-module ,_module))

;;; *******
;;; PRINTER
;;; *******

(defun print-module-object (obj stream &rest ignore)
  (declare (ignore ignore)
	   (type module obj)
	   (type stream stream)
	   (values t))
  (if (or (module-is-inconsistent obj)
	  (null (module-name obj)))
      (format stream "[:module \"~a\"]" (module-name obj))
    (cond ((module-is-object obj)
	   (format stream ":mod![\"~a\"]" (module-print-name obj)))
	  ((module-is-theory obj)
	   (format stream ":mod*[\"~a\"]" (module-print-name obj)))
	  (t (format stream ":mod[\"~a\"]" (module-print-name obj))))))

;;; *********************************
;;; Constructing RUN TIME ENVIRONMENT -----------------------------------------
;;; *********************************

;;; see "globals.lisp" for about run time environment.
;;; *current-module*       : the module 
;;; *current-sort-order*   : transitive closure of sort relations of the current
;;;                          module. 
;;; *current-opinfo-table* : operator information table of the current module .
;;;

(defmacro with-in-module ((_module_) &body body)
  (once-only (_module_)
    ` (block with-in-module
	(let* ((*current-module* ,_module_)
	       (*current-sort-order* (module-sort-order *current-module*))
	       (*current-opinfo-table* (module-opinfo-table *current-module*))
	       (*current-ext-rule-table* (module-ext-rule-table *current-module*)))
	    (declare (special *current-module*
			      *current-sort-order*
			      *current-opinfo-table*
			      *current-ext-rule-table*))
	    ;;
	    ,@body))))

(defun change-current-module (mod)
  (declare (type (or null module) mod)
	   (values t))
  (when mod
    (setf *current-module* mod
	  *current-sort-order* (module-sort-order mod)
	  *current-opinfo-table* (module-opinfo-table mod)
	  *current-ext-rule-table* (module-ext-rule-table mod))
    mod))

;;; *********
;;; MODULE DB___________________________________________________________________
;;; *********

;;; *MODULES-SO-FAR-TABLE*
;;; mapping : normalized module expression -> modules.
;;; * see normoexp.lisp for mormalization.
;;;-----------------------------------------------------------------------------
(declaim (type list *modules-so-far-table*))

(defvar *modules-so-far-table* nil)

(defun add-modexp-defn (modexp value)
  (add-to-assoc-table *modules-so-far-table* modexp value))

(defun find-global-module (modexp)
  (find-in-assoc-table *modules-so-far-table* modexp))

;;; The intent is that the following be used with uncanonicalized module
;;; name's.; case in particular -- creation of parameters for module
;;;
;;; (declaim (inline equal-top-level))
#-gcl
(defun equal-top-level (x y)
  (cond ((stringp x) (equal x y))
	((atom x) (eql x y))
	((atom y) nil)
	(t (and (equal-top-level (car x) (car y))
		(equal-top-level (cdr x) (cdr y))))))

#+gcl
(si::define-inline-function equal-top-level (x y)
  (cond ((stringp x) (equal x y))
	((atom x) (eql x y))
	((atom y) nil)
	(t (and (equal-top-level (car x) (car y))
		(equal-top-level (cdr x) (cdr y))))))

(defun find-equivalent-module-in-env (me)
  (dolist (entry *modules-so-far-table*)
    (let ((key (car entry))
	  (val (cdr entry)))
      (when (equal-top-level me key)
	(return-from find-equivalent-module-in-env val))))
  nil)

;;; used in eval-module
;;;
(defun modexp-update-name (modexp modval)
  (let ((entry (rassoc modval *modules-so-far-table*)))
    (when entry
      (setf (car entry) modexp)
      (return-from modexp-update-name nil))
    (with-output-panic-message ()
      (format t "modexp-update-name: no such module ~a" modval)
      (chaos-error 'panic))))

;;; *MODEXP-LOCAL-TABLE*
;;; 'Local' extension to *MODULES-SO-FAR-TABLE* used for parameters of pushed
;;; modules. 
;;; conicalized module expressions -> modules.
;;;-----------------------------------------------------------------------------
(declaim (type list *modexp-local-table*))

(defvar *modexp-local-table* nil)

(defun add-modexp-local-defn (key value)
  (add-to-assoc-table *modexp-local-table* key value))

(defun get-modexp-local (key)
  (find-in-assoc-table *modexp-local-table* key))

;;; *MODEXP-EVAL-TALBLE*
;;;-----------------------------------------------------------------------------
(declaim (type list *modexp-eval-table*))

(defvar *modexp-eval-table* nil)

(defun find-modexp-eval (modexp)
  (find-in-assoc-table *modexp-eval-table* modexp))

(defun add-modexp-eval (modexp value)
  (add-to-assoc-table *modexp-eval-table* modexp value))

(defun clear-modexp-eval () (setq *modexp-eval-table* nil))

;;;-----------------------------------------------------------------------------
;;; FIND-MODULE-IN-ENV : modexp -> { module | nil }
;;;
(defun find-module-in-env (me &optional (context *current-module*))
  (declare (type (or null module) context))
  (if context
      (or (get-modexp-local (list me (module-name context)))
	  (find-modexp-eval me)
	  (find-global-module me))
      (or (find-modexp-eval me)
	  (find-global-module me))))

(defun find-module-in-env-ext (name &optional (context *current-module*)
				    no-error)
  (declare (type (or module simple-string) name)
	   (type (or null module) context))
  ;; 
  (when (module-p name)
    (return-from find-module-in-env-ext name))
  ;;
  (when context
    (when (equal name (module-name context))
      (return-from find-module-in-env-ext context)))
  ;;
  (let ((quals (parse-with-delimiter name #\.)))
    ;; scan qualifires from right to left
    ;; the last one is the target we are looking for.
    (let ((c context)
	  (tmod nil))
      (dolist (qname (reverse quals))
	(let ((subs (module-all-submodules c)))
	  (setq tmod (or (find-module-in-sublist qname subs c)
			 ;; Wed Feb 17 13:27:44 JST 1999
			 ;; (find-module-in-env qname c)
			 nil))
	  (unless tmod
	    (when no-error
	      (return-from find-module-in-env-ext nil))
	    ;; (break)
	    (with-output-chaos-error ('no-such-module)
	      (format t "no such module ~a in the context "
		      qname)
	      (print-mod-name context *standard-output* t)
	      ))
	  (when (atom tmod) (setq tmod (list tmod)))
	  (when (cdr tmod)
	    (with-output-chaos-error ('ambiguous-module-name)
	      (format t "module name ~a is ambiguous in the context."
		      qname)
	      (print-mod-name context *standard-output* t)
	      ))
	  (setq c (car tmod))))
      (car tmod))))

(defun find-module-in-sublist (name subs &optional (context *current-module*))
  (let ((res nil))
    (when context
      (let ((als (rassoc name (module-alias context) :test #'equal)))
	(when als
	  (push (car als) res))))
    (dolist (sub subs)
      (let* ((smod (car sub))
	     (sname (module-name smod)))
	;; we eliminate :using
	(unless (eq (cdr sub) :using)
	  (cond ((modexp-is-parameter-theory sname)
		 (if (equal name (car sname))
		     (pushnew smod res)))
		(t (if (equal name sname)
		       (pushnew smod res)))))))
    res))

;;; **************
;;; INITIALIZATION _____________________________________________________________
;;; **************

;;; method chaches (see "boperator.lisp")
(defvar .method1. nil)
(defvar .method-tab1. nil)
(defvar .method-val1. nil)
(defvar .method2. nil)
(defvar .method-tab2. nil)
(defvar .method-val2. nil)

(defun clear-method-info-hash ()
  (setf .method1. nil
	.method-tab1. nil
	.method-val1. nil
	.method2. nil
	.method-tab2. nil
	.method-val2. nil))

;;; INITIALIZE-MODULE

(defun initialize-module (mod)
  (declare (type module mod)
	   (values t))
  ;;
  (setf (module-status mod) -1)		; initial state.
  (setf (module-decl-form mod) nil)
  ;; interface
  (if (the (or null ex-interface) (module-interface mod))
      (initialize-module-interface mod)
      (setf (module-interface mod) (make-ex-interface)))
  (initialize-depend-dag mod)
  ;; signature
  (if (the (or null signature-struct) (module-signature mod))
      (initialize-signature (module-signature mod))
      (setf (module-signature mod) (make-signature-struct :module mod)))
  ;; axiom set
  (setf (module-theorems mod) nil)
  (if (the (or null axiom-set) (module-axiom-set mod))
      (initialize-axiom-set (module-axiom-set mod))
      (setf (module-axiom-set mod) (make-axiom-set :module mod)))
  ;; parse infos
  (if (the (or null parse-dictionary) (module-parse-dictionary mod))
      (initialize-parse-dictionary (module-parse-dictionary mod))
      (setf (module-parse-dictionary mod) (make-parse-dictionary)))
  ;; misc infos
  (setf (object-misc-info mod) nil)
  ;;; (if (object-misc-info mod)
  ;;;    (initialize-module-ex-info (module-ex-info mod))
  ;;;    (setf (module-ex-info mod) (make-module-ex-info)))
  ;; trs
  (if (the (or null trs) (module-trs mod))
      (initialize-trs (module-trs mod) mod)
      (setf (module-trs mod) (make-trs :module mod)))
  ;; context
  (if (the (or null module-context) (module-context mod))
      (initialize-module-context (module-context mod))
      (setf (module-context mod) (make-module-context)))
  ;; symbol table
  (setf (module-alias mod) nil)
  (setf (module-symbol-table mod) (make-symbol-table))
  ;; print name
  ;; (setf (module-print-name mod) (make-module-print-name2 mod))
  (setf (module-print-name mod) (make-module-print-name mod))
  ;;
  (clear-tmp-sort-cache)
  (clear-method-info-hash))

;;; CLEAN-UP-MODULE
;;; trash all away from module.
;;;
(defun clean-up-module (mod)
  (when (null (module-name mod))
    (return-from clean-up-module nil))
  (setf (module-name mod) nil)
  (setf (module-status mod) 0)
  (setf (module-decl-form mod) nil)
  ;; interface
  (if (module-interface mod)
      (clean-up-ex-interface (module-interface mod)))
  (setf (module-interface mod) nil)
  ;; signature
  (if (module-signature mod)
      (clean-up-signature (module-signature mod)))
  (setf (module-signature mod) nil)
  ;; axiom set
  (setf (module-theorems mod) nil)
  (if (module-axiom-set mod)
      (clean-up-axiom-set (module-axiom-set mod)))
  (setf (module-axiom-set mod) nil)
  ;; parse infos
  (if (module-parse-dictionary mod)
      (clean-up-parse-dictionary (module-parse-dictionary mod)))
  (setf (module-parse-dictionary mod) nil)
  ;; misc infos
  (setf (object-misc-info mod) nil)
  ;; trs
  (if (module-trs mod)
      (clean-up-trs (module-trs mod)))
  (setf (module-trs mod) nil)
  ;; context
  (if (module-context mod)
      (clean-up-context (module-context mod)))
  (setf (module-context mod) nil)
  ;;
  (clear-tmp-sort-cache)
  (clear-method-info-hash))

;;; EOF
