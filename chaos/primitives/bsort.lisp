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
				File: bsort.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;=============================================================================
;;;				      SORT
;;;=============================================================================

;;; ****************************************************************************
;;; STRUCTURE DEFINITIONS & BASIC OPERATIONS  **********************************
;;; ON SORTS *******************************************************************

;;; ************
;;; SORT-STRUCT ________________________________________________________________ 
;;; ************
;;; Structure SORT is the basis of all types of sorts. This defines
;;; common structure of body parts of various type of sort term.
;;;
;;; There are some special sorts, i.e., and-sort, or-sort, err-sort, reocord,
;;; and class. These are defined by extending the sort-struct.
;;;
;;; NOTE: sort-struct is a template for common structure, and its instance will
;;;       never be created as a term body (abstract class).
;;;

(defstruct (sort-struct (:conc-name "SORT-STRUCT-")
			(:include object (-type 'sort-struct))
			(:copier nil)
			(:print-function print-sort-internal)
			(:constructor make-sort-struct)
			(:constructor sort-struct* (id hidden)))
  (id nil :type symbol)
  (hidden nil :type (or null t))
  (constructor nil :type list)
  (inhabited nil :type (or null t))
  (derived-from nil :type (or null sort-struct)))

(eval-when (:execute :load-toplevel :compile-toplevel)
(defmacro sort-module (sort)
  `(object-context-mod ,sort))
)

(eval-when (:execute :load-toplevel)
  (setf (symbol-function 'sort-sort-struct) (symbol-function 'sort-struct-p))
  (setf (get 'sort-struct :eval) nil)
  (setf (get 'sort-struct :print) 'print-sort-internal))

;;; ****
;;; SORT ____________________
;;; ****
;;;;  the structure of nomal user defined sort.
;;;   all of the user defines sorts (except record and class) are
;;;   generated as an instace of term with gensort as its body part.
;;;-----------------------------------------------------------------------------

(defstruct (sort* (:include sort-struct (-type 'sort))
		  (:conc-name "SORT-")
		  (:copier nil)
		  (:constructor make-sort)
		  (:constructor sort* (id &optional hidden))
		  (:predicate sort-p)
		  (:print-function print-sort-object))
  )

(eval-when (:execute :load-toplevel)
  (setf (symbol-function 'is-sort) (symbol-function 'sort-p))
  (setf (get 'sort :type-predicate) (symbol-function 'sort-p))
  (setf (get 'sort :eval) nil)
  (setf (get 'sort :print) 'print-sort-internal))

;;; Common sort accessors -----------------------------------------------------

(defmacro sort-type (_sort-body) `(object-type ,_sort-body))
(defmacro sort-name (_sort-body) `(sort-id ,_sort-body)) ; synonym
(defmacro sort-is-inhabited (_sort-body) `(sort-inhabited ,_sort-body))
(defmacro sort-is-hidden (_sort-body) `(sort-hidden ,_sort-body))
(defmacro sort-is-visible (_sort-body) `(not (sort-hidden ,_sort-body)))
(defmacro sort-visible-type (_sort-body)
  `(if (sort-is-hidden ,_sort-body)
       :hidden
       :visible))

(defmacro sort-constructors (_sort-body)
  `(sort-constructor ,_sort-body))

(defun sort-is-derived-from (sort)
  (let ((df (sort-derived-from sort)))
    (if df
	(or (sort-is-derived-from df)
	    df)
	nil)))

(defun get-original-sort (sort)
  (let ((res sort))
    (loop (if (null (sort-derived-from res))
	      (return nil)
	      (setq res (sort-derived-from res))))
    res))

;;; Type predicates -----------------------------------------------------------

(defmacro sort-is-user-defined? (_s)
  `(memq (sort-type ,_s) '(sort bsort class-sort record-sort)))

;;; Printer -------------------------------------------------------------------

(defun sort-visible-type-print (sort)
  (declare (type sort-struct sort)
	   (values symbol))
  (if (sort-is-hidden sort)
      :h
      :v))

(defun print-sort-object (obj stream &rest ignore)
  (declare (ignore ignore))
  (let ((name (concatenate 'string (string (sort-id obj)) "." (module-print-name (sort-module obj)))))
    (if (sort-is-hidden obj)
	(format stream ":hsort[~s]" name)
      (format stream ":sort[~s]" name))))

;;; Constructor ----------------------------------------------------------------
(defun new-general-sort (id module &optional hidden)
  (declare (type symbol id)
	   (type module module)
	   (type (or null t) hidden))
  (let ((sort (sort* id hidden)))
    (setf (sort-module sort) module)
    (set-object-context-module sort module)
    sort))

;;; *SORT-TABLE*

(defvar *sort-table* nil)
(defun get-sort-named (sort-name module)
  (declare (type symbol sort-name)
	   (type module module)
	   (values (or null sort-struct)))
  (find-in-assoc-table *sort-table* (cons sort-name module)))

(defun clear-tmp-sort-cache () (setq *sort-table* nil))
(defun register-sort-cache (sort)
  (declare (type sort-struct sort)
	   (values t))
  (add-to-assoc-table *sort-table* (cons (sort-id sort)
					(sort-module sort))
		      sort))

;;; ************
;;; RECORD&CLASS________________
;;; ************
;;; structure of instances of record or classe sorts. inherits %sort.
;;;
;;; additional slots:
;;;   slots    : slot information
;;;   idconstr : class/record id constructor,
;;;              a pair of (method . pattern-variable).  
;;;   constr   : class/record constructor method.
;;;   maker    : list of methods for make.Foo operations.
;;; 
;;; slot information is a list of slot-info, which is a 6-tuple
;;; (slot-name sort default attribute-constructor reader writer), where
;;;  0  slot-name     : slots' name, a string.
;;;  1  sort          : the sort of the slot's value.
;;;  2  default       : the default value (pre-term, i.e., string or sequence of
;;;                     tokens.)
;;;  3  attribute-id  : the attribute name constructor,
;;;                     a pair of (method . pattern-variable).
;;;  4  reader        : attribute reader method.
;;;  5  writer        : attribute writer method.
;;;
;;; * NOTE * `pattern-variable's are used for constructing record/class
;;; template term (generalizing constructor terms in axioms).
;;; 

(defstruct (crsort (:include sort* (-type 'crsort))
		   (:copier nil)
		   (:constructor make-crsort)
		   (:constructor crsort* (id &optional hidden))
		   (:print-function print-cr-sort-object))
  (slots nil :type list)		; slot informations.
  (idconstr nil :type list)		; id constructor info.
  (constr nil :type t)			; term constructor method.
  (maker nil :type list)		; list of methods for `make.Foo'
					; operations. 
  (copy	nil :type (or null t))		; t iff the sort is a copy.
  )

(eval-when (:execute :load-toplevel)
  (setf (get 'crsort :print) 'print-sort-internal)
  (setf (symbol-function 'is-crsort) (symbol-function 'crsort-p))
  (setf (get 'crsort :type-predicate) (symbol-function 'crsort-p))
  )

(defun print-cr-sort-object (obj stream &rest ignore)
  (print-sort-object obj stream ignore))

;;; Class sort _________________
;;;           

(defstruct (class-sort (:include crsort (-type 'class-sort))
		       (:copier nil)
		       (:constructor make-class-sort)
		       (:constructor class-sort* (id &optional hidden))
		       (:print-function print-class-sort-object))
  )

(eval-when (:execute :load-toplevel)
  (setf (get 'class-sort :type-predicate) (symbol-function 'class-sort-p))
  (setf (symbol-function 'is-class-sort) (symbol-function 'class-sort-p))
  (setf (get 'class-sort :print) 'print-sort-internal))

(defun print-class-sort-object (obj stream &rest ignore)
  (print-sort-object obj stream ignore))

;;; Record sort ________________

(defstruct (record-sort (:include crsort (-type 'record-sort))
			(:constructor make-record-sort)
			(:constructor record-sort* (id &optional hidden))
			(:print-function print-record-sort-object)
			(:copier nil))
  )

(eval-when (:execute :load-toplevel)
  (setf (get 'record-sort :type-predicate)
	(symbol-function 'record-sort-p))
  (setf (get 'record-sort :print) 'print-sort-internal)
  (setf (symbol-function 'is-record-sort)
	(symbol-function 'record-sort-p)))

(defun print-record-sort-object (obj stream &rest ignore)
  (print-sort-object obj stream ignore))

;;; Primitive structure accessors ----------------------------------------------

;;; (defmacro crsort-slots (_s) `(%crsort-slots ,_s))
;;; (defmacro crsort-id (_s) `(crsort-idconstr ,_s))
;;; (defmacro crsort-constr (_s) `(crsort-constr ,_s))
(defmacro crsort-constr-method (_s) `(crsort-constr ,_s)) ; synonym
(defmacro crsort-id-method (_s) `(car (crsort-idconstr ,_s)))
(defmacro crsort-id-variable (_s) `(cdr (crsort-idconstr ,_s)))
;;; (defmacro crsort-maker (_s) `(%crsort-maker ,_s))
(defmacro crsort-make-1 (_s) `(car (crsort-maker ,_s)))
(defmacro crsort-make-2 (_s) `(cadr (crsort-maker ,_s)))
;;; (defmacro crsort-copy (_s) `(crsort-copy ,_s))
(defmacro crsort-is-a-copy (_s) `(crsort-copy ,_s))

;;; the following two are only for class sort
(defmacro crsort-make-3 (_s) `(caddr (crsort-maker ,_s)))
(defmacro crsort-make-4 (_s) `(cadddr (crsort-maker ,_s)))

;;; Primitive Constructors -----------------------------------------------------

(defun create-cr-sort (p-type id module constructor inhabited slots hidden)
  (declare (type symbol p-type id)
	   (type module module)
	   (type t constructor)
	   (type (or null t) inhabited hidden)
	   (type list slots)
	   (values crsort))
  (let ((s (if (eq p-type 'class-sort)
	       (class-sort* id)
	       (record-sort* id))))
    (setf (sort-module s) module
	  (sort-constructor s) constructor
	  (sort-inhabited s) inhabited
	  (crsort-slots s) slots
	  (crsort-hidden s) hidden)
    (setf (crsort-maker s) (if (eq p-type 'class-sort)
			       (list nil nil nil nil)
			       (list nil nil)))
    (set-object-context-module s module)
    s))
  
(defun new-record-sort (id module &optional hidden)
  (declare (type symbol id)
	   (type module module)
	   (type (or null t) hidden)
	   (values crsort))
  (create-cr-sort 'record-sort		; type
		  id			; id
		  module		; 
		  nil			; constructor
		  nil			; inhabited
		  nil			; slots
		  hidden))

(defun new-class-sort (id module &optional hidden)
  (declare (type symbol id)
	   (type module module)
	   (type (or null t) hidden)
	   (values crsort))
  (create-cr-sort 'class-sort
		  id
		  module
		  nil
		  nil
		  nil
		  hidden))

;;; Type Predicates ------------------------------------------------------------

;;; (defmacro crsort-p (_s)
;;;   `(and (chaos-object? ,_s) (memq (object-type ,_s) '(record-sort
;;; 						          class-sort)))) 
;;; (defmacro record-sort-p (_s) `(is-record-sort ,_s))
;;; (defmacro class-sort-p (_s)  `(is-class-sort ,_s))

;;; Accessors For Slot Informations --------------------------------------------

(defmacro find-slot-info (slot-name sort) ` (assoc ,slot-name (crsort-slots ,sort)
						   :test #'equal))
(defmacro cr-slot-name (_slot-info) `(car ,_slot-info))
(defmacro cr-slot-sort (_slot-info) `(cadr ,_slot-info))
(defmacro cr-slot-default (_slot-info) `(caddr ,_slot-info))
(defmacro cr-slot-attribute-id (_slot-info) `(cadddr ,_slot-info))
(defmacro cr-slot-attribute-id-method (_slot-info) `(car (cadddr ,_slot-info)))
(defmacro cr-slot-attribute-id-variable (_slot-info) `(cdr (cadddr ,_slot-info)))
(defmacro cr-slot-reader (_slot-info) `(nth 4 ,_slot-info))
(defmacro cr-slot-writer (_slot-info) `(nth 5 ,_slot-info))

;;; getting infos via slot-name.

(defmacro get-slot-sort (_slot-name _s)
  `(cr-slot-sort (find-slot-info ,_slot-name ,_s)))
(defmacro get-slot-default (_slot-name _s)
  `(cr-slot-default (find-slot-info ,_slot-name ,_s)))
(defmacro get-attribute-id (_slot-name _s)
  `(cr-slot-attribute-id (find-slot-info ,_slot-name ,_s)))
(defmacro get-attribute-id-method (_slot-name _s)
  `(cr-slot-attribute-id-method (find-slot-info ,_slot-name ,_s)))
(defmacro get-attribute-id-variable (_slot-name _s)
  `(cr-slot-attribute-id-variable (find-slot-info ,_slot-name ,_s)))
(defmacro get-slot-reader (_slot-name _s)
  `(cr-slot-reader (find-slot-info ,_slot-name ,_s)))
(defmacro get-slot-writer (_slot-name _s)
  `(cr-slot-writer (find-slot-info ,_slot-name ,_s)))

;;; *****
;;; BSORT____________________
;;; *****
;;; the structure of builtin sorts. inherits sort-struct.
;;; additional slot:
;;;  info -- BSORT-INFO see below for the definition.
;;;

(defstruct (bsort (:include sort* (-type 'bsort))
		  (:copier nil)
		  (:constructor make-bsort)
		  (:constructor bsort* (id &optional hidden))
		  (:print-function print-bsort-object))
  (info nil :type list))

(eval-when (:execute :load-toplevel)
  (setf (symbol-function 'is-bsort) (symbol-function 'bsort-p))
  (setf (get 'bsort :type-predicate) (symbol-function 'bsort-p))
  (setf (get 'bsort :print) 'print-bsort-internal))

(defun print-bsort-object (obj stream &rest ignore)
  (print-sort-object obj stream ignore))

;;; (defmacro bsort-hidden (_s) `(%bsort-hidden ,_s))
;;; (defmacro bsort-info (_s) `(%bsort-info ,_s))

;;; Primitive Constructor ------------------------------------------------------

(defun new-bi-sort (id module &optional info hidden)
  (declare (type symbol id)
	   (type module module)
	   (type list info)
	   (type (or null t) hidden)
	   (values bsort))
  (let ((bs (bsort* id hidden)))
    (setf (sort-module bs) module
	  (bsort-info bs) info)
    (set-object-context-module bs module)
    bs))

;;; Predicate ------------------------------------------------------------------

;;; (defmacro  bsort-p (_obj) `(is-bsort ,_obj))
(defmacro sort-is-builtin (_*bsort)  `(bsort-p ,_*bsort)) ; snonym

;;; BSORT-INFO : 
;;; ( token-preciate-function : given token, return t iff the token is of
;;;                             constant of the builtin sort.
;;;   term-creator-function   : given token, creates an instance of this builtin
;;;                             sort. 
;;;   term-printer-function   : given term, print it.
;;;   term-predicate-function  : given term, returns t iff the term is of this
;;;                             builtin sort. 
;;; )
;;;
(defmacro bsort-token-predicate (bsort_)  `(car (bsort-info ,bsort_)))
(defmacro bsort-term-creator (bsort_)  `(second (bsort-info ,bsort_)))
(defmacro bsort-term-printer (bsort_)  `(third (bsort-info ,bsort_)))
(defmacro bsort-term-predicate (bsort_)  `(fourth (bsort-info ,bsort_)))

;;; *BUILTIN-SORT-TABLE* holds all of the builtin sorts.

(defvar *builtin-sort-table* nil)

(defun get-builtin-sort-named (sort-name)
  (declare (type symbol sort-name)
	   (values (or null bsort)))
  (find-in-assoc-table *builtin-sort-table* sort-name #'eq))

(defun register-builtin-sort (sort)
  (declare (type bsort sort)
	   (values t))
  (add-to-assoc-table *builtin-sort-table* (sort-id sort) sort #'eq))

(defun clear-builtin-sorts ()
  (declare (values t))
  (setq *builtin-sort-table* nil))

;;; ********
;;; AND-SORT_________________
;;; ********
;;; An and-sort represents an intersection of its component sorts.
;;; Used for regularizing signatures or for realizing SEMANTIC sorts due to
;;; equations. (Corresponds to GLB of its components).
;;; This type of sorts are generated internally.
;;;

(defstruct (and-sort (:include sort* (-type 'and-sort))
		     (:copier nil)
		     (:constructor make-and-sort)
		     (:constructor and-sort* (id &optional hidden))
		     (:print-function print-and-sort-object))
  (components nil :type list))

(eval-when (:execute :load-toplevel)
  (setf (get 'and-sort :type-predicate)
	(symbol-function 'and-sort-p))
  (setf (symbol-function 'is-and-sort)
	(symbol-function 'and-sort-p))
  (setf (get 'and-sort :print)
	'print-and-sort-internal))

(defun print-and-sort-object (obj stream &rest ignore)
  (print-sort-object obj stream ignore))

;;; Primitive accessors --------------------------------------------------------

;;; (defmacro and-sort-components (_and-sort) `(%and-sort-components ,_and-sort))

;;; Primitive constructors -----------------------------------------------------

(defun new-and-sort (id &optional module and-components hidden)
  (declare (type symbol id)
	   (type (or null module) module)
	   (type list and-components)
	   (type (or null t) hidden)
	   (values and-sort))
  (let ((as (and-sort* id hidden)))
    (setf (sort-module as) module
	  (and-sort-components as) and-components)
    (set-object-context-module as module)
    as))

;;; Predicates -----------------------------------------------------------------

;;; (defmacro and-sort-p (_object) `(is-and-sort ,_object))

#|| not used
(defmacro is-and-sort-term (term)
  (once-only (term)
    `(and (term? ,term) (and-sort-p (term-body ,term)))))
||#

;;; *******
;;; OR-SORT__________________
;;; *******
;;; An `or-sort' represents a disjoint sum of its component sorts.
;;; Used for implementing ERR-SORT (or more generally, corresponds to LUB of
;;; its components).
;;; This type of sorts are also generated internally only.
;;;

(defstruct (or-sort (:include sort* (-type 'or-sort))
		    (:copier nil)
		    (:constructor make-or-sort)
		    (:constructor or-sort* (id &optional hidden))
		    (:print-function print-or-sort-object))
  (components nil :type list))

(eval-when (:execute :load-toplevel)
  (setf (get 'or-sort :type-predicate) (symbol-function 'or-sort-p))
  (setf (get 'or-sort :print) 'print-or-sort-internal)
  (setf (symbol-function 'is-or-sort)
	(symbol-function 'or-sort-p)))

(defun print-or-sort-object (obj stream &rest ignore)
  (print-sort-object obj stream ignore))

;;; Primitve accessors ---------------------------------------------------------

;;; (defmacro or-sort-components (_or-sort)
;;;  `(%or-sort-components ,_or-sort))

;;; Primitve constructor -------------------------------------------------------

(defun new-or-sort (id &optional module or-components hidden)
  (declare (type symbol id)
	   (type (or null module) module)
	   (type list or-components)
	   (type (or null t) hidden)
	   (values or-sort))
  (let ((os (or-sort* id hidden)))
    (setf (sort-module os) module
	  (or-sort-components os) or-components)
    (set-object-context-module os module)
    os))

;;; Predicate ------------------------------------------------------------------

;;; (defmacro or-sort-p (_object) `(is-or-sort ,_object))

;;; ********
;;; ERR-SORT_________________
;;; ********
;;; An `err-sort' is for allowing ILL-SORTED terms and keeps clean semantics.
;;; For each connected component of subsort relation, an err-sort is generated
;;; at the top (see `generate-err-sorts' in "sort.lisp").
;;;

(defstruct (err-sort (:include sort* (-type 'err-sort))
		     (:copier nil)
		     (:constructor make-err-sort)
		     (:constructor err-sort* (id &optional hidden))
		     (:print-function print-err-sort-object))
  (components nil :type list)
  (lowers nil :type list))

(eval-when (:execute :load-toplevel)
  (setf (get 'err-sort :type-predicate) (symbol-function 'err-sort-p))
  (setf (get 'err-sort :print) 'print-err-sort-internal)
  (setf (symbol-function 'is-err-sort) (symbol-function 'err-sort-p)))

(defun print-err-sort-object (obj stream &rest ignore)
  (print-sort-object obj stream ignore))

;;; Primitve accessors ---------------------------------------------------------

;;; (defmacro err-sort-components (_err-sort)
;;;   `(%err-sort-components ,_err-sort))

;;; (defmacro err-sort-subsorts (_err-sort)
;;;  `(err-sort-lowers ,_err-sort))

;;; Primitive Constructor ------------------------------------------------------

(defun new-err-sort (id &optional module components lowers hidden)
  (declare (type symbol id)
	   (type (or null module) module)
	   (type list components lowers)
	   (type (or null t) hidden)
	   (values err-sort))
  (let ((es (err-sort* id hidden)))
    (setf (sort-module es) module
	  (err-sort-components es) components
	  (err-sort-lowers es) lowers)
    (set-object-context-module es module)
    es))

;;; Predicates ----------------------------------------------------------------

;;; (defmacro err-sort-p (_object) `(is-err-sort ,_object))

;;; ********************
;;; EQUALITY AMONG SORTS______________
;;; ********************

;;; SORT= s1 s2
;;; returns t iff s1 and s2 are identical sorts.
;;;
(defmacro sort= (_s1 _s2) `(eq ,_s1 ,_s2))
    
;;; function version of sort=.
;;;(defun sort=* (s1 s2) (term-builtin-eq s1 s2))
(defun sort=* (s1 s2) (eq s1 s2))

(defmacro sort-set-equal (_s1 _s2)
  (once-only (_s1 _s2)
   ` (if (< (length ,_s1) (length ,_s2))
	 (null (set-difference ,_s2 ,_s1 :test #'sort=*))
	 (null (set-difference ,_s1 ,_s2 :test #'sort=*)))))

(defmacro sort-list= (sl1_ sl2_) `(equal ,sl1_ ,sl2_))

;;;=============================================================================
;;;			   SORT RELATION & SORT ORDER
;;;=============================================================================

;;;   All of the sorts of a signature is gathered and stored in order according
;;;   to their subsort relation.
;;;   We implement this sotore as a table indexed by the sort object and each of
;;;   the entry has the structure
;;;       [Sort, Subsorts, Supersorts, ERR-SORT]
;;;   we call this a SORT-RELATION.
;;;   Both subsorts and supersorts represent a transitive closure derived from
;;;   subsort declarations which include the sort, and are its lower sorts and
;;;   greater sorts respectively.
;;;   ERR-SORT is a special kind of sort which is generated .....

;;;
;;;   It is a lattice, i.e., there are builtin sorts (the-universal-sort),
;;;   and (the-bottom-sort).

;;;                        UNIVERSAL and BOTTOM SORT
;;;    Universal sort is a sort symbol which denotes the sort of whole universe.
;;;    The name `TERM' is protected and preserved from renaming and redeclaring.
;;;    Bottom sort is a sort symbol which is

;;; *************
;;; SORT RELATION__________________
;;; *************
;;;   ( sort subsorts supersorts err-sort )

;;; Constructor

(defmacro make-sort-relation (_sort &optional _sub _super _err-sort)
  `(list ,_sort ,_sub ,_super ,_err-sort))

(defmacro copy-sort-relation (_sl)  `(copy-tree ,_sl))

;;; Accessors

(defmacro sort-relation-sort (_sl) `(car ,_sl))
(defmacro _subsorts (_sl) `(cadr ,_sl))
(defmacro _supersorts (_sl) `(caddr ,_sl))
(defmacro _err-sort (_sl) `(cadddr ,_sl))

;;; little utils

(defun elim-sys-sorts-from-relation (sl)
  (declare (type list sl)
	   (values list))
  (macrolet ((pure? (_sl)
	       ` (dolist (_s ,_sl t)
		   (when (sort-is-for-regularity? _s) (return nil))))
	     (rem-sys (_sl)
	       `(remove-if #'(lambda (x) (sort-is-for-regularity? x)) ,_sl)))
    (let ((s (sort-relation-sort sl))
	  (subs (_subsorts sl))
	  (sups (_supersorts sl)))
      (when (sort-is-for-regularity? s)
	(return-from elim-sys-sorts-from-relation nil))
      (make-sort-relation s
			  (if (pure? subs) subs (rem-sys subs))
			  (if (pure? sups) sups (rem-sys sups))))))

;;; **********
;;; SORT-ORDER__________________
;;; **********
(deftype sort-order () 'hash-table)

;;; ALLOCATOR

(defun allocate-sort-order ()
  (declare (values sort-order))
  (make-hash-table :test #'eq))

(defun clear-sort-order (sorder)
  (declare (type sort-order sorder)
	   (values t))
  (clrhash sorder))

;;; GET SORT'S RELATION FROM SORT ORDER.

(defmacro get-sort-relation (_sort _sort-order)
  `(gethash ,_sort ,_sort-order))

;;; COPIER :

;;; construct new sort order which is logically equal to given order.
;;; *NOTE* sorts are not copied.

(defun copy-sort-order (sort-order)
  (declare (type sort-order sort-order)
	   (values sort-order))
  (let ((new-order (allocate-sort-order)))
    (maphash #'(lambda (s sl)
		 (setf (gethash s new-order) (copy-list sl)))
	     sort-order)
    new-order))

(defun get-all-sorts (sort-order)
  (declare (type sort-order sort-order)
	   (values list))
  (let ((res nil))
    (maphash #'(lambda (ss sl)
		 (declare (ignore sl))
		 (push ss res))
	     sort-order)
    res))

;;; ACCESSORS via SORT

(defmacro subsorts (_sort &optional (_sort-order '*current-sort-order*))
  (once-only (_sort)
    ` (if (err-sort-p ,_sort)
	  (err-sort-lowers ,_sort)
	  (_subsorts (get-sort-relation ,_sort ,_sort-order)))))

(defmacro sub-or-equal-sorts (_sort &optional (_sort-order '*current-sort-order*))
  (once-only (_sort)
    ` (if (err-sort-p ,_sort)
	  (cons ,_sort (err-sort-lowers ,_sort))
	  (let ((.sort-relation. (get-sort-relation ,_sort ,_sort-order)))
	    (cons ,_sort
		  (_subsorts .sort-relation.))))))

(defmacro supersorts (_sort &optional (_sort-order '*current-sort-order*))
   (once-only (_sort _sort-order)
     ` (if (err-sort-p ,_sort)
	   nil
	   (let (($sl (get-sort-relation ,_sort ,_sort-order)))
	     (or (and (_err-sort $sl)
		      (cons (_err-sort $sl) (_supersorts $sl)))
		 (_supersorts $sl))))))

(defmacro supersorts-no-err (_sort &optional (_sort-order '*current-sort-order*))
  (once-only (_sort _sort-order)
    ` (if (err-sort-p ,_sort)
	  nil
	  (let (($sl (get-sort-relation ,_sort ,_sort-order)))
	    (_supersorts $sl)))))

(defmacro super-or-equal-sorts (_sort &optional (_sort-order '*current-sort-order*))
  (once-only (_sort)
    ` (if (err-sort-p ,_sort)
	  (list ,_sort)
	  (let ((.sort-relation. (get-sort-relation ,_sort ,_sort-order)))
	    (cons ,_sort
		  (or (and (_err-sort .sort-relation.)
			   (cons (_err-sort .sort-relation.)
				 (_supersorts .sort-relation.)))
		      (_supersorts .sort-relation.)))))))

(defun the-err-sort (sort &optional (sort-order *current-sort-order*))
  (declare (type sort* sort)
	   (type sort-order sort-order))
  (cond ((sort= sort *universal-sort*) sort)
	((sort= sort *huniversal-sort*) sort)
	((sort= sort *cosmos*) sort)
	((sort= sort *bottom-sort*) sort)
	(t (if (err-sort-p sort)
	       sort
	     (_err-sort (get-sort-relation sort sort-order))))))

(defsetf the-err-sort (__sort &optional (__sort-order *current-sort-order*))
    (__value)
  `(setf (_err-sort (get-sort-relation ,__sort ,__sort-order)) ,__value))

;;; ******************************
;;; BASIC SORT RELATION PREDICATES ____________
;;; ******************************

;;; SORT< sort1 sort2 sort-order
;;; returns t iff the first sort is strictly lower than the second.
(declaim (inline sort<))
#-GCL
(defun sort< (s1 s2 &optional (sort-order *current-sort-order*))
  (declare (type sort* s1 s2)
	   (type sort-order sort-order)
	   (values (or null t)))
  (and (not (sort= s1 s2))
       (or (sort= s2 *cosmos*)
	   (if (sort-is-hidden s1)
	       (if (sort= s2 *huniversal-sort*)
		   t
		 (if (sort= s1 *huniversal-sort*)
		     nil
		   (memq s2 (supersorts s1 sort-order))))
	     (if (sort= s2 *universal-sort*)
		 t
	       (if (sort= s1 *universal-sort*)
		   nil
		 (if (sort= s1 *bottom-sort*)
		     t
		   (if (sort= s2 *bottom-sort*)
		       nil
		     (memq s2 (supersorts s1 sort-order))))))))))
  
#+GCL
(defmacro sort< (s1 s2 &optional (sort-order '*current-sort-order*))
  (once-only (s1 s2)
    ` (and (not (sort= ,s1 ,s2))
	   (or (sort= ,s2 *cosmos*)
	       (if (sort-is-hidden ,s1)
		   (if (sort= ,s2 *huniversal-sort*)
		       t
		     (if (sort= ,s1 *huniversal-sort*)
			 nil
		       (memq ,s2 (supersorts ,s1 ,sort-order))))
		 (if (sort= ,s2 *universal-sort*)
		     t
		   (if (sort= ,s1 *universal-sort*)
		       nil
		     (if (sort= ,s1 *bottom-sort*)
			 t
		       (if (sort= ,s2 *bottom-sort*)
			   nil
			 (memq ,s2 (supersorts ,s1 ,sort-order)))))))))))

;;; function version
(defun sort<* (s1 s2 &optional (sort-order *current-sort-order*))
  (declare (type sort* s1 s2)
	   (type sort-order sort-order)
	   (values (or null t)))
  (sort< s1 s2 sort-order))

;;; SORT<= sort1 sort2 sort-order
;;; retrns t iff the second sort is in the relexive transitive closure of
;;; greater sorts of the first one.
(defmacro sort<= (_s1 _s2 &optional (_sort-order '*current-sort-order*))
  (once-only (_s1 _s2)
    ` (or (sort= ,_s1 ,_s2)
	  (sort< ,_s1 ,_s2 ,_sort-order))))

;;; it's function version.
(defun sort<=* (s1 s2 &optional (sort-order *current-sort-order*))
  (declare (type sort* s1 s2)
	   (type sort-order sort-order)
	   (values (or null t)))
  (or (sort= s1 s2) (sort< s1 s2 sort-order)))

;;; SORT-IS-IN sort sort-set sort-order
;;; returns t if the given sort is greater or lower than one of the sort in the
;;; sort-set.
;;; NOTE: assumes that sort-set does not include *unversal-sort* nor *bottom-sort*.
;;;
(defmacro sort-is-in (_s _sort-set &optional (_sort-order '*current-sort-order*))
  (once-only (_s _sort-set _sort-order)
    ` (and ,_sort-set
	   (dolist (.s1. ,_sort-set nil)
	     (if (or (sort= ,_s .s1.)
		     (member ,_s (subsorts .s1. ,_sort-order) :test #'eq)
		     (member ,_s (supersorts .s1. ,_sort-order) :test #'eq))
		 (return t))))))

;;; SORT-LIST<= sort-list1 sort-list2 sort-order
;;;  returns t iff each elements of sort-list1 is a subsort of
;;;  corresponding sort of sort-list2.
;;;
(defun sort-list<= (lst1 lst2 &optional (so *current-sort-order*))
  (declare (type list lst1 lst2)
	   (type sort-order so)
	   (values (or null t)))
  (loop (when (null lst1)(return (null lst2)))
	(when (null lst2)(return (null lst1)))
	(unless (sort<= (car lst1) (car lst2) so)
	  (return nil))
	(setq lst1 (cdr lst1))
	(setq lst2 (cdr lst2))))

(defun sort-list<=-any (lst1 lst2 &optional (so *current-sort-order*))
  (declare (type list lst1 lst2)
	   (type sort-order so)
	   (values (or null t)))
  (loop (when (null lst1)(return (null lst2)))
	(when (null lst2)(return (null lst1)))
    (unless (or (sort= *cosmos* (car lst1))
		(sort<= (car lst1) (car lst2) so))
	  (return nil))
	(setq lst1 (cdr lst1))
	(setq lst2 (cdr lst2))))


;;; SORT-LIST< sort-list1 sort-list2 sort-order
;;;  returns t iff each elements of sort-list1 is a proper subsort of
;;;  corresponding sort of sort-list2.
;;;
(defun sort-list< (lst1 lst2 &optional (so *current-sort-order*))
  (declare (type list lst1 lst2)
	   (type sort-order so)
	   (values (or null t)))
  (loop (when (null lst1)(return (null lst2)))
	(when (null lst2)(return (null lst1)))
	(unless (sort< (car lst1) (car lst2) so)
	  (return nil))
	(setq lst1 (cdr lst1))
	(setq lst2 (cdr lst2))))

;;; ********************
;;; SORT-ORDER UTILITIES______________
;;; ********************

;;; ADD-SORT-TO-ORDER sort sort-order
;;; makes the new enty for sort in sort-order.
;;; if the sort has alredy its entry, do nothing.
;;;
(defun add-sort-to-order (sort &optional (sort-order *current-sort-order*))
  (declare (type sort* sort)
	   (type sort-order sort-order)
	   (values t))
  (let ((ent (get-sort-relation sort sort-order)))
    (unless ent
      (add-relation-to-order (make-sort-relation sort nil nil) sort-order))))
  
;;; ADD-RELATION-TO-ORDER sort-relation sort-order
;;; adds the sort-relation to sort-order.
;;;
(defun gather-connected-relations-from-order (relation
					      &optional
					      (sort-order *current-sort-order*))
  (declare (type list relation)
	   (type sort-order sort-order)
	   (values list))
  (macrolet ((pushnew-relation (__?rel __?res)
	       ` (pushnew ,__?rel ,__?res :test #'eq)))
    (let ((res nil)
	  (s (sort-relation-sort relation))
	  (subs (_subsorts relation))
	  (sups (_supersorts relation)))
      (pushnew-relation (get-sort-relation s sort-order) res)
      (dolist (ls subs)
	(pushnew-relation (get-sort-relation ls sort-order) res))
      (dolist (gs sups)
	(pushnew-relation (get-sort-relation gs sort-order) res))
      res)))

(defun add-relation-to-order (sort-relation
			      &optional (sort-order *current-sort-order*))
  (declare (type list sort-relation)
	   (type sort-order sort-order)
	   (values sort-order))
  (let* ((sort (sort-relation-sort sort-relation))
	 (subs (_subsorts sort-relation))
	 (supers (_supersorts sort-relation)))
    (declare (type sort* sort)
	     (type list subs supers))
    (when (or (sort= sort *universal-sort*) (sort= sort *bottom-sort*)
	      (sort= sort *huniversal-sort*) (sort= sort *hbottom-sort*)
	      (sort= sort *cosmos*))
      (return-from add-relation-to-order sort-order))
    ;;
    (macrolet ((ls-union (_s _ls)
		 ` (let ((..sl (get-sort-relation ,_s sort-order)))
		     (pushnew ,_ls (_subsorts ..sl) :test #'eq)))
	       (gs-union (_s _gs)
		 ` (let ((..sl (get-sort-relation ,_s sort-order)))
		     (pushnew ,_gs (_supersorts ..sl) :test #'eq))))
      ;; merge new realtion
      (let ((o-sort-rel (get-sort-relation sort sort-order)))
	(declare (type list o-sort-rel))
	(if o-sort-rel
	    (progn
	      (setf (_subsorts o-sort-rel)
		    (union subs (_subsorts o-sort-rel) :test #'eq))
	      (setf (_supersorts o-sort-rel)
		    (union supers (_supersorts o-sort-rel) :test #'eq)))
	    (progn
	      (setf (get-sort-relation sort sort-order) sort-relation)
	      (setf o-sort-rel sort-relation
		    subs (_subsorts sort-relation)
		    supers (_supersorts sort-relation)))))
      ;; we must gather relations which can be affected by new relation,
      ;; then compute transitive relations among them.
      (let ((rels (gather-connected-relations-from-order sort-relation sort-order)))
	(declare (type list rels))
	(dolist (sl rels)
	  (let ((nsubs (_subsorts sl))
		(nsups (_supersorts sl)))
	    (declare (type list nsubs nsups))
	    (dolist (s1 nsubs)
	      (dolist (s2 nsups)
		(ls-union s2 s1)
		  (gs-union s1 s2))))))
      sort-order)))

;;; MAX-MINORANTS sort-set sort-order
;;;  compute the set of maximal elements in the set of lower bounds
;;;  of the given sort-set using the relation contained in the sort-order.
;;;
(defun max-minorants (sort-set order)
  (declare (type sort-order order)
	   (type list sort-set)
	   (values list))
  (labels ((inter-lower (set)
	     (declare (type list set)
		      (values list))
	     ;;  compute the set of lower bounds of a given set of sorts.
	     ;;  If this set is empty returns nil.
	     (if (cdr set)
		 (intersection (sub-or-equal-sorts (car set) order)
			       (inter-lower (cdr set))
			       :test #'sort=*)
		 (if set
		     (sub-or-equal-sorts (car set) order)
		     nil))))
    (let ((max-min nil)
	  (lower-bounds (inter-lower sort-set)))
      (declare (type list max-min lower-bounds))
      (dolist (s lower-bounds max-min)
	(unless (intersection (supersorts s order) lower-bounds :test #'eq)
	  (setq max-min (adjoin s max-min :test #'sort=*)))))))

;;; MAXIMAL-SORTS sorts order
;;; Finds all the sorts in a list which are greater than all other comparable
;;; sorts in the list.
;;;
(defun maximal-sorts (sorts order)
  (declare (type list sorts)
	   (type sort-order order)
	   (values list))
  (let ((maximal nil))
    (dolist (s sorts maximal)
      (unless (intersection (supersorts s order) sorts :test #'eq)
	(pushnew s maximal :test #'eq)))))

(defun maximal-sorts-no-error (sorts order) ; version avoiding error sorts.
  (declare (type list sorts)
	   (type sort-order order)
	   (values list))
  (let ((maximal nil))
    (dolist (s sorts maximal)
      (unless (intersection (supersorts-no-err s order) sorts :test #'eq)
	(pushnew s maximal :test #'eq)))))

;;; MINIMAL-SORTS sorts order
;;; Finds all the sorts in a list which are lesser than all other comparable
;;; sorts in the list.
;;;
(defun minimal-sorts (sorts order)
  (declare (type list sorts)
	   (type sort-order order)
	   (values list))
  (let ((minimal nil))
    (declare (type list minimal))
    (dolist (s sorts minimal)
      (unless (intersection (subsorts s order) sorts :test #'eq)
	(pushnew s minimal :test #'eq)))))

;;; MEET-OF-SORTS sort1 sort2 order
;;; Finds the list of sorts which are maximal but less than or equal to
;;; the two given sorts.
;;; This function as it stands, and thus does not create the actual GLB sort,
;;; but generates the maximal declared sorts containted in the GLB sort.
;;;
(defun meet-of-sorts (sort1 sort2 &optional (sort-order *current-sort-order*))
  (declare (type sort* sort1 sort2)
	   (type sort-order sort-order))
  (cond ((sort<= sort1 sort2) (list sort1))
	((sort< sort2 sort1 sort-order) (list sort2))
	(t (maximal-sorts (intersection (subsorts sort1) (subsorts sort2))
			  sort-order))))

;;; MERGET-SORT-RELATIONS sort-relations1 sort-relations2
;;; *NOTE* sort-relations2 is destructively modified.
;;;
(defun merge-sort-relations (sl1 sl2)
  (declare (type list sl1 sl2)
	   (values list))
  (unless sl1 (return-from merge-sort-relations sl2))
  (dolist (sort-relation sl1)
    (let ((xsort-rel (assq (sort-relation-sort sort-relation) sl2)))
      (if xsort-rel
	  (progn
	    (setf (_subsorts xsort-rel)
		  (union (_subsorts sort-relation)
			 (_subsorts xsort-rel) :test #'eq))
	    (setf (_supersorts xsort-rel)
		  (union (_supersorts sort-relation)
			 (_supersorts xsort-rel) :test #'eq)))
	  (push sort-relation sl2))))
  sl2)

;;; MERGE-SORT-ORDER order1 order2
;;; Merges two sort order `order1' and `order2'.
;;; As a result, `order2' is destructively modified and returned.
;;;
(defun merge-sort-order (order1 order2)
  (declare (type (or null sort-order) order1)
	   (type sort-order order2)
	   (values sort-order))
  (unless order1 (return-from merge-sort-order order2))
  (maphash #'(lambda (sort sort-relation)
	       (declare (type sort* sort)
			(type list sort-relation)
			(values t))
	       (let ((xsort-rel (get-sort-relation sort order2)))
		 (if xsort-rel
		     (progn
		       (setf (_subsorts xsort-rel)
			     (union (_subsorts sort-relation)
				    (_subsorts xsort-rel) :test #'eq))
		       (setf (_supersorts xsort-rel)
			     (union (_supersorts sort-relation)
				    (_supersorts xsort-rel) :test #'eq)))
		     (setf (get-sort-relation sort order2) sort-relation))))
	   order1)
  order2)

(defun merge-sort-order-no-extra (order1 order2)
  (declare (type (or null sort-order) order1)
	   (type sort-order order2)
	   (values sort-order))
  (unless order1 (return-from merge-sort-order-no-extra order2))
  (macrolet ((filter-out-ordinal-sorts (___sort-list)
	       ` (remove-if #'(lambda (s) (sort-is-for-regularity? s))
			    ,___sort-list)))
    (maphash #'(lambda (sort sort-relation)
		 (declare (type sort* sort)
			  (type list sort-relation))
		 (unless (or (and-sort-p sort) (or-sort-p sort))
		   (let ((xsort-rel (get-sort-relation sort order2)))
		     (declare (type list xsort-rel))
		     (if xsort-rel
			 (progn
			   (setf (_subsorts xsort-rel)
				 (filter-out-ordinal-sorts
				  (union (_subsorts sort-relation)
					 (_subsorts xsort-rel) :test #'eq)))
			 (setf (_supersorts xsort-rel)
			       (filter-out-ordinal-sorts
				(union (_supersorts sort-relation)
				       (_supersorts xsort-rel) :test #'eq))))
		       (setf (get-sort-relation sort order2) sort-relation)))))
	   order1)
  order2))

;;;  IS-IN-SAME-CONNECTED-COMPONENT : sort1 sort2 sort-order -> Bool
;;;	check if sort1 and sort2 is in same sort hierarchy
;;;  *NOTE* : assume error sorts are already genrated.
;;;
(defun is-in-same-connected-component (s1 s2 sort-order)
  (declare (type sort* s1 s2)
	   (type sort-order sort-order)
	   (values (or null t)))
  (or (sort= s1 s2)
      (if (or (sort= s1 *cosmos*) (sort= s2 *cosmos*))
	  t
	(and (eq (sort-is-hidden s1) (sort-is-hidden s2))
	     (or (if (sort-is-hidden s1)
		     (or (sort= *huniversal-sort* s1)
			 (sort= *huniversal-sort* s2)
			 (sort= *hbottom-sort* s1)
			 (sort= *hbottom-sort* s2))
		   (or (sort= *universal-sort* s1)
		       (sort= *universal-sort* s2)
		       (sort= *bottom-sort* s1)
		       (sort= *bottom-sort* s2)))
		 (if (err-sort-p s1)
		     (sort= s1 (the-err-sort s2 sort-order))
		   (if (err-sort-p s2)
		       (sort= (the-err-sort s1 sort-order) s2)
		     (sort= (the-err-sort s1 sort-order)
			    (the-err-sort s2 sort-order)))))))))

;;; COMPONENT-TOP  : sort sort-order -> sort
;;;  returns the greatest sorts of given sort
;;;
(defun component-top (sort sort-order)
  (declare (type sort* sort)
	   (type sort-order sort-order)
	   (values list))
  (maximal-sorts (supersorts-no-err sort sort-order) sort-order))

;;; IS-IN-SAME-CONNECTED-COMPONENT* : Sort Sort SortOrder -> Bool
;;; like `is-in-same-connected-component' but does not assume
;;; error-sort.
;;;
(defun is-in-same-connected-component* (s1 s2 so)
  (declare (type sort* s1 s2)
	   (type sort-order so)
	   (values (or null t)))
  (or (eq s1 s2)
      (if (or (eq s1 *cosmos*) (eq s2 *cosmos*))
	  t
	  (and (eq (sort-is-hidden s1) (sort-is-hidden s2))
	       (cond ((err-sort-p s1)
		      (if (err-sort-p s2)
			  nil
			  (let ((lowers (err-sort-lowers s1)))
			    (intersection lowers
					  (sub-or-equal-sorts s2 so)))))
		     ((err-sort-p s2)
		      (let ((lowers (err-sort-lowers s2)))
			(intersection lowers
				      (sub-or-equal-sorts s1 so))))
		     (t (or (if (sort-is-hidden s1)
				(or (sort= *huniversal-sort* s1)
				    (sort= *huniversal-sort* s2)
				    (sort= *hbottom-sort* s1)
				    (sort= *hbottom-sort* s2))
				(or (sort= *universal-sort* s1)
				    (sort= *universal-sort* s2)
				    (sort= *bottom-sort* s1)
				    (sort= *bottom-sort* s2)))
			    (sort<= s1 s2 so)
			    (sort<= s2 s1 so)
			    (have-common-subsort s1 s2 so)
			    (let ((t1 (component-top s1 so)))
			      (and t1 (sort-set-equal t1
						      (component-top s2 so)))))))))))

;;; HAVE-COMMON-SUBSORT : Sort Sort SortOrder -> Bool
;;;
(defun have-common-subsort (s1 s2 so)
  (declare (type sort* s1 s2)
	   (type sort-order so)
	   (values (or null t)))
  (let ((ss1 (subsorts s1 so))
	(ss2 (subsorts s2 so)))
    (dolist (s ss1 nil)
      (declare (type sort* s))
      (when (memq s ss2) (return t)))))

;;; ALL-SORTS-IN-ORDER (&optional (sort-order *current-sort-order*))
;;;
(defun all-sorts-in-order (&optional (sort-order *current-sort-order*))
  (declare (type sort-order sort-order)
	   (values list))
  (let ((res nil))
    (maphash #'(lambda (sort relation)
		 (declare (ignore relation))
		 (push sort res))
	     sort-order)
    res))

;;; TOP-COMPONENTS sort-order
;;;
(defun top-components (&optional (sort-order *current-sort-order*))
  (declare (type sort-order sort-order)
	   (values list))
  (maximal-sorts (let ((res nil))
		   (maphash #'(lambda (sort relation)
				(declare (ignore relation))
				(push sort res))
			    sort-order)
		   res)
		 sort-order))

;;; BOTTOM-COMPONENTS sort-order
;;;
(defun bottom-components (&optional (sort-order *current-sort-order*))
  (declare (type sort-order sort-order)
	   (values list))
  (minimal-sorts (let ((res nil))
		   (maphash #'(lambda (sort relation)
				(declare (ignore relation))
				(push sort res))
			    sort-order)
		   res)
		 sort-order))

;;; DIRECT-SUBSORTS sort sort-order
;;; returns the list of sorts which are direct subsorts
;;;
(defun direct-subsorts (sort &optional (sort-order *current-sort-order*))
  (declare (type sort* sort)
	   (type sort-order sort-order)
	   (values list))
  (maximal-sorts (subsorts sort sort-order) sort-order))

;;; DIRECT-SUPERSORTS sort sort-order
;;;
(defun direct-supersorts (sort &optional (sort-order *current-sort-order*))
  (declare (type sort*)
	   (type sort-order sort-order)
	   (values list))
  (minimal-sorts (supersorts sort sort-order) sort-order))

;;; DIRECT-SUPERSORTS-NO-ERR
;;;
(defun direct-supersorts-no-err (sort &optional (sort-order *current-sort-order*))
  (declare (type sort* sort)
	   (type sort-order sort-order)
	   (values list))
  (minimal-sorts (supersorts-no-err sort sort-order) sort-order))

#||
 ;;;  DELETE-SORT-FROM-ORDER sort sort-order
 ;;;  returns sort-order after eliminating sort.
 ;;;
 (defun delete-sort-from-order (sort sort-order)
   (remhash sort sort-order)
   (maphash #'(lambda (ss sort-rel)
		  (declare (ignore ss))
		  (setf (_subsorts sort-rel)
			(delete sort (_subsorts sort-rel) :test #'eq))
		  (setf (_supersorts sort-rel)
		      (delete sort (_supersorts sort-rel) :test #'eq)))
	     sort-order)
   (update-sort-order sort-order)
   sort-order)
||#

;;; SORT-RELATIONS-TRANSITIVE-CLOSURE sort-relations1 sort-relations2
;;;  sort-relations2 is destructively modified.
;;;
#||
(defun sort-order-transitive-closure (previous-order new-order)
  (flet ((ls-union (order s ls)
	   ;; make the union of the sorts lower than "s" with ls.
	   (let ((sl (get-sort-relation s order)))
	     (setf (_subsorts sl)
		   (union (_subsorts sl) ls :test #'eq))))
	 (gs-union (order s gs)
	   ;; make the union of the sorts greater than "s" with gs.
	   (let ((sl (get-sort-relation s order)))
	     (setf (_supersorts sl)
		   (union (_supersorts sl) gs :test #'eq)))))
    (let ((closure (merge-sort-order previous-order new-order)))
      (declare (type sort-order closure))
      (maphash #'(lambda (sort sort-rel)
		   (declare (ignore sort))
		   (let ((ls (_subsorts sort-rel))
			 (gs (_supersorts sort-rel)))
		     (dolist (s1 ls)
		       (dolist (s2 gs)
			 (declare (type sort* s2))
			 (ls-union closure s2 (list s1))
			 (gs-union closure s1 (list s2))))))
	       closure)
      ;; generates erro sorts.
      (generate-err-sorts closure)
      closure)))

||#

(defun sort-relations-transitive-closure (sl1 sl2)
  (declare (type list sl1 sl2)
	   (values list))
  (flet ((ls-union (relations s ls)
	   (declare (type list relations ls)
		    (type sort* s)
		    (values list))
	   ;; make the union of the sorts lower than "s" with ls.
	   (let ((sl (assq s relations)))
	     (declare (type list sl))
	     (unless sl (break "Panic no sort relation(ls)!"))
	     (setf (_subsorts sl)
		   (union (_subsorts sl) ls :test #'eq))))
	 (gs-union (relations s gs)
	   (declare (type list relations gs)
		    (type sort* s)
		    (values list))
	   ;; make the union of the sorts greater than "s" with gs.
	   (let ((sl (assq s relations)))
	     (declare (type list sl))
	     (unless sl (break "Panic no sort relation(gs)!"))
	     (setf (_supersorts sl)
		   (union (_supersorts sl) gs :test #'eq)))))
    (let ((p-closure (merge-sort-relations sl1 sl2)))
      (declare (type list p-closure))
      (dolist (sort-rel p-closure) 
	(let ((ls (_subsorts sort-rel))
	      (gs (_supersorts sort-rel)))
	  (declare (type list ls gs))
	  (dolist (s1 ls)
	    (declare (type sort* s1))
	    (dolist (s2 gs)
	      (declare (type sort* s2))
	      (ls-union p-closure s2 (list s1))
	      (gs-union p-closure s1 (list s2))))))
      p-closure)))

(defun sort-relations-transitive-closure1 (sl)
  (declare (type list sl)
	   (values list))
  (sort-relations-transitive-closure nil sl))

;;; CHECK-CYCLIC-SORT-ORDER sort-order
;;;
(defun check-cyclic-sort-order (sort-order)
  (declare (type sort-order sort-order)
	   (values t))
  (maphash #'(lambda (ss sort-relation)
	       (when (member ss (_subsorts sort-relation) :test #'eq)
		 (with-output-chaos-warning ()
		   (princ "cycle in sort order structure : ")
		   (princ (string (sort-id ss)))
		   (princ " appears in its lowers."))))
	   sort-order))

;;; ERROR SORT UTILS

;;; CLEAR-ERR-SORTS : sort-order -> sort-order'
;;;
(defun clear-err-sorts (sort-order)
  (declare (type sort-order sort-order)
	   (values t))
  (maphash #'(lambda (s sl)
	       (declare (ignore s))
	       (setf (_err-sort sl) nil))
	   sort-order)
  sort-order)

;;; GET-KINDS  : SortOrder -> LIST[(err-sort subsort-list)]
;;;
(defun get-kinds (sort-order)
  (declare (type sort-order sort-order)
	   (values list))
  (let ((res nil))
    (maphash #'(lambda (s sl)
		 (declare (type sort* s)
			  (type list sl))
		 (let ((es (_err-sort sl)))
		   (declare (type (or null err-sort) es))
		   (when (and es (not (or (eq s *universal-sort*)
					  (eq s *bottom-sort*)
					  (eq s *huniversal-sort*)
					  (eq s *hbottom-sort*)
					  (eq s *cosmos*))))
		     (let ((pre (assoc es res :test #'eq)))
		       (declare (type list pre))
		       (if pre
			   (pushnew s (cdr pre) :test #'eq)
			   (push (cons es (list s)) res))))))
	     sort-order)
    res))

;;; GET-ERR-SORTS
;;;
(defun get-err-sorts (sort-order)
  (declare (type sort-order sort-order)
	   (values list))
  (let ((res nil))
    (maphash #'(lambda (s sl)
		 (declare (ignore s))
		 (let ((es (_err-sort sl)))
		   (when es (pushnew es res :test #'eq))))
	     sort-order)
    res))

;;; GET-FAMILY : ErroSort SortOrder -> List[Sort]
;;;
(defun get-family (err-sort so)
  (declare (type err-sort err-sort)
	   (type sort-order so)
	   (values list))
  (let ((res nil))
    (maphash #'(lambda (s sl)
		 (declare (type sort* s)
			  (type list sl)
			  (values list))
		 (when (sort= err-sort (_err-sort sl))
		   (pushnew s res :test #'eq)))
	     so)
    res))


;;; EOF
