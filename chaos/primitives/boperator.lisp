;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
;;; $Id: boperator.lisp,v 1.6 2010-08-01 06:32:28 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: primitives
			      File: boperator.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;; STRUCTURE & BASIC OPERATORS ON OPERATORS ***********************************
;;;                                METHODS *************************************
;;;*****************************************************************************

;;;=============================================================================
;;; 			      OPERATORS & friends
;;;=============================================================================

;;; An operator is a folder which holds each specific operations (methods)
;;; with the same syntactic form in a module.
;;; An operator is created per one syntactic form in a module, that is,
;;; operator declarations which define the same syntactic form are gethered
;;; then configured into an operator. 
;;; For a Chaos language construct, operator names are used for referring
;;; a set of methods. The rule determining what methods are in a set is
;;; rather complex: 
;;; (1) if a module does not import other modules: (this is a rare case,
;;;    because most of the modules are imports builtin BOOL implicitly)
;;;    methods with the same form are in the same set of methods.
;;; (2) if a module does import other modules:
;;;    operator declarations satisfying the following properties belong
;;;    to an operator:
;;;    (i) define the same syntax : same number of arguments, same
;;;        form (prefix or mixfix).
;;;    (ii) coarities are in a same connected component.
;;; The methods which belong to an operator is accessed via `opinfo'
;;; (see below for the definition). This is because the set of methods
;;; can varie among modules.
;;;
;;; The name consists of `symbol' and `number of arguments' it accepts,
;;; and this pair is hold in the slot `name'. 
;;; The macro `operator-name' returns the list of `symbol' and `number of arguments'.
;;; The value of `operator-name' is canonicalized, i.e., the same name can be
;;; compaired by EQ (see `canonicalize-op-name' of below).
;;; The following macros are used for access the component of the identifier:
;;;   operator-symbol : operator symbol -- list of string, 
;;;                   e.g., '("if" "_" "then" "_" "else" "_" "fi")
;;;   operator-num-args : 
;;;              number of arguments the operator accepts(natural number).
;;;              the special symbol '*' means that the operator accepts
;;;              sequence of arguments of various length (not implemented
;;;              yet.) 
;;;
;;; The operator is identified by its name and the module in which it is created.
;;; `operator-id' returns this info as a pair of operator name and module:
;;;        ((symbol . number-of-args) . module)
;;;
;;; Together with these, we collect `default values' of attributes
;;; of methods declared by an `attribute declaration'.
;;;      strategy : rewrite strategy supplied by user (a list of naturals or nil)
;;;      theory   : special equational theory of the operator, assoc, comm, id ..
;;;      syntax   : syntax of the operator.
;;;      memo     : t iff memoize the rewriting.
;;;      print-name: operator's print name (string).
;;;      hidden   : t iff the operator is bhavioural operator.

;;; ********
;;; OPSYNTAX
;;; ********
;;; - gathers syntactical information of an operator, i.e., a set of
;;;   methods with the same syntactic form.
;;; - stored as an attribute of operator object (slot syntax).
;;; *NOTE*
;;; the slots token-seq, mixfix, and assoc is common to all methods,
;;; prec and cprec are used for `default' value for methods.
;;;
(defstruct opsyntax
  (token-seq nil :type list)		; list of terminal(string)s and arguments'
					; place holders (symbol T).
					; ex. ("if" T "then" T "else" T "fi")
					; means that the operator has a syntax
					; <if_then_else_fi> ::= "if" term "then"
					;                       term "else" term
					;                       "fi"
  (mixfix nil :type (or null t))	; T iff the syntax is `mixfix'.
  (type nil :type symbol)		; one of 'juxtaposition, 'latefix, 'antefix.
  (prec nil :type (or null fixnum))	; parsing precedence of the operator.
  (cprec nil :type (or null fixnum))
					; computed prec, used by `simple-parser'.
  (assoc nil :type symbol)		; associativity of the operator,
					; 'l-assoc or 'r-assoc.
  )


;;; ********
;;; OPERATOR __________________________________________________________________
;;; ********
#||
(defterm operator (object)		; (static-object)
  :visible (name)			; list of `symbol' & `number of arguments'.
  :hidden (module
	   strategy
	   theory
	   syntax
	   memo
	   print-name
	   hidden
	   )
  :int-printer print-operator-object
  :print print-operator-internal)

||#

(defstruct (operator (:include object (-type 'operator))
		     (:constructor make-operator)
		     (:constructor operator* (name))
		     (:copier nil)
		     (:print-function print-operator-object))
  (name nil :type list)
  (module nil :type (or null module))
  (strategy nil :type list)
  (theory nil :type (or null op-theory))
  (syntax nil :type (or null opsyntax))
  (print-name nil :type t) 
  (hidden nil :type (or null t))
  )

(eval-when (eval load)
  (setf (symbol-function 'is-operator) (symbol-function 'operator-p))
  (setf (get 'operator :type-predicate) (symbol-function 'operator-p))
  (setf (get 'operator :print) 'print-operator-internal))

(defun print-operator-object (obj stream &rest ignore)
  (declare (ignore ignore))
  (format stream "(:op ~s : ~x)" (operator-name obj) (addr-of obj))
  )

;;; (defmacro operator-p (_o) `(is-operator ,_o))

;;; Basic accessors ----------------------------------------------------------

;;; (defmacro operator-name (_operator) `(%operator-name ,_operator))
(defmacro operator-symbol (_operator) `(car (operator-name ,_operator)))
(defmacro operator-num-args (_operator) `(cdr (operator-name ,_operator)))
;;; (defmacro operator-module (_operator) `(%operator-module ,_operator))
;;; (defmacro operator-hidden (_operator) `(%operator-hidden ,_operator))

;;; id = (name . module)
(defmacro operator-id (__operator)
  (once-only (__operator)
    `(cons (operator-name ,__operator) (operator-module ,__operator))))
(defmacro operator-module-id (__operator) `(module-name (operator-module
						        ,__operator))) 
;;; (defmacro operator-strategy (__operator) `(%operator-strategy ,__operator))
(defmacro operator-rewrite-strategy (__operator)
  `(operator-strategy ,__operator)) 
;;; (defmacro operator-theory (__operator) `(%operator-theory ,__operator))
;;; (defmacro operator-syntax (__operator) `(%operator-syntax ,__operator))
;;; (defmacro operator-print-name (__operator) `(%operator-print-name ,__operator))
;;; (defmacro operator-memo (__operator) `(%operator-memo ,__operator))

(defun explode-operator-name (op-symbol)
  (declare (type list op-symbol)
	   (values list))
  (mapcar #'(lambda (s) (if (equal s "_")
			    t
			    s))
	  op-symbol))

(defun make-operator-token-seq (operator)
  (declare (type operator operator)
	   (values list))
  (explode-operator-name (operator-symbol operator)))

(defun operator-syntactic-type-from-name (token-seq)
  (declare (type list token-seq)
	   (values symbol))
  (if (eq t (car token-seq))
      (if (eq t (cadr token-seq))
	  'juxtaposition
	  'latefix)
      'antefix))

;;; Predicate ------------------------------------------------------------------
;;; identity

;;; OPERATOR=
;;; OPERATOR-EQL
;;; returns t iff the operators have the same syntax (the same token
;;; sequence, the same number of arugments. 
;;; The following code uses `eq' for comparing names. This is guaranteed,
;;; because the operator names are canonicalized (see "biterm.lisp").
;;;
(defmacro operator= (_o1 _o2) `(eq ,_o1 ,_o2))
(defmacro operator-eql (_op1 _op2)
  `(eq (operator-name ,_op1) (operator-name ,_op2)))

;;; OPERATOR-EQUAL 
;;; returns t iff two operator has the same identifier.
;;;
(defmacro operator-equal (op1_ op2_)
  (once-only (op1_ op2_)
    ;; just the same as (equal (operator-id op1) (operator-id op2))
    ;; but little bit faster...
    ` (and (operator-eql ,op1_ ,op2_)
	   (eq (operator-module ,op1_) (operator-module ,op2_)))))

;;; OPERATOR-IS-BEHAVIOURAL
;;;
(defmacro operator-is-behavioural (op)
  `(operator-hidden ,op))

;;; Constructor of Operator body.-----------------------------------------------
(defvar *opname-table* nil)
#||
(eval-when (eval load)
  (setf *opname-table* (make-hash-table :test #'equal)))
||#

(defun canonicalize-op-name (name)
  (declare (type list name)
	   (values list))
  (or (cdr (assoc name *opname-table* :test #'equal))
      (prog1
	  name
	(push (cons name name) *opname-table*))))

#||
(defvar .operator-recycler.)
(eval-when (eval load)
  (setq .operator-recycler. (make-hash-table :test #'equal)))

(defun allocate-operator (name num-args module)
  (let* ((name (canonicalize-op-name (cons name num-args)))
	 (key (cons name module))
	 (op (gethash key .operator-recycler.)))
    (if op
	op
	(progn
	  (setq op (operator* name))
	  (setf (operator-module op) module)
	  (when (modexp-is-simple-name (module-name module))
	    (setf (gethash key .operator-recycler.) op))
	  op))))

||#

(defun allocate-operator (name num-args module)
  (declare (type list name)
	   (type fixnum num-args)
	   (type module module)
	   (values operator))
  (let ((name (canonicalize-op-name (cons name num-args)))
	(op nil))
    (setq op (operator* name))
    (setf (operator-module op) module)
    op))

(defun new-operator (&key name num-args
			  module strategy theory syntax print-name)

  (declare (type list name)
	   (type (or null fixnum) num-args)
	   (type (or null module) module)
	   (type (or null list) strategy)
	   (type (or null op-theory) theory)
	   (type t print-name)
	   (values operator))
  (let ((o (allocate-operator name num-args module)))
    (setf (operator-strategy o) strategy
	  (operator-theory o) theory
	  (operator-syntax o) syntax
	  (operator-print-name o) print-name)
    o))


;;; accessors of an operator's syntax via operator.
;;;
(defmacro operator-token-sequence (_*operator)
  `(opsyntax-token-seq (operator-syntax ,_*operator)))

(defmacro operator-is-mixfix (_*operator)
  `(opsyntax-mixfix (operator-syntax ,_*operator)))

(defmacro operator-syntactic-type (_*operator)
  `(opsyntax-type (operator-syntax ,_*operator)))

(defmacro operator-precedence (_*operator)
  `(opsyntax-prec (operator-syntax ,_*operator)))

(defmacro operator-computed-precedence (_*operator)
  `(opsyntax-cprec (operator-syntax ,_*operator)))

(defmacro operator-associativity (_*operator)
  `(opsyntax-assoc (operator-syntax ,_*operator)))

(defun make-print-operator-id (op-nam)
  (declare (type t op-nam))
  (cond ((and (consp op-nam)
	      (stringp (car op-nam)))
	 (if (cdr op-nam)
	     (reduce #'(lambda (a b)
			 (declare (type (or simple-string symbol) a b))
			 (concatenate 'string
				      (the simple-string (string a))
				      (the simple-string (string b))))
		     op-nam)
	     (the simple-string (car op-nam))))
	((symbolp op-nam) (string (the symbol op-nam)))
	(t (break "Internal error: invalid op-nam ~S" op-nam))))

(defun cmake-operator-print-name (operator)
  (declare (type operator operator)
	   (values simple-string))
  (let ((nam (operator-name operator))
	(mixfix (operator-is-mixfix operator)))
    (if mixfix
	(make-print-operator-id (car nam))
	(format nil "~a/~d"
		(make-print-operator-id (car nam))
		(cdr nam)))))

;;; ******
;;; OPINFO
;;; ******

;;; Internal data structure. Represents module DEPENDENT information of an
;;; operator. NOT term, i.e., does not appear explicitly in Chaos programs.
;;; Its a pair of
;;;     operator     : an operator object.
;;;     methods      : list of operator-method.
;;;     method-table : a table for method look up.

;;; constructor
(defun make-opinfo (&key operator methods method-table)
  (declare (type (or null operator) operator)
	   (type list methods)
	   (type list method-table)
	   (values list))
  (list operator methods method-table))

(defun opinfo-p (object)
  (declare (type t object)
	   (values (or null t)))
  (and (listp object)
       (listp (cdr (last object)))
       (= 3 (length object))
       (operator-p (car object))))

;;; accessors
(defmacro opinfo-operator (_info) `(car ,_info))
(defmacro opinfo-methods (_info) `(the list (cadr ,_info)))
(defmacro opinfo-method-table (_info) `(caddr ,_info))

;;; The list of opinfo is hold in the slot `all-operators' of a module object.
;;; (see the definition of `module' object below).

;;; operator-info : operator list-of-infos -> { opinfo | nil }
;;; 
(defmacro get-operator-info (_*operator _*infos)
  `(car (member ,_*operator ,_*infos :test #'(lambda (x y)
					   (operator= x (opinfo-operator y))))))

;;; The following accessors accepts operator object and the list of opinfo.
;;;
(defmacro operator-methods (operator_* infos_*)
  `(opinfo-methods (get-operator-info ,operator_* ,infos_*)))
(defmacro operator-method-table (operator_* infos_*)
  `(opinfo-method-table (get-operator-info ,operator_* ,infos_*)))

;;; ***************
;;; OPERATOR THEORY
;;; ***************
;;; equational theories. see `op-theory.lisp" for internal data structures and
;;; operations.
;;;
;;; [ assoc comm id(r): CONST ]

(defmacro operator-theory-info (_*operator)
  `(theory-info (operator-theory ,_*operator)))

(defmacro operator-is-associative (_*operator)
  `(theory-contains-associativity (operator-theory ,_*operator)))

(defmacro operator-is-identity (_*operator)
  `(theory-contains-identity (operator-theory ,_*operator)))

(defmacro operator-is-commutative (_*operator)
  `(theory-contains-commutativity (operator-theory ,_*operator)))

;;; ******
;;; METHOD
;;; ******

;;; An operator is a collection of operator declarations with the same syntax.
;;; One declarion together with its axioms define the syntax and semantics
;;; of an operation as a part. Thus we can think the operator as `generic'
;;; operation and one operator declaration with corresponding axioms as
;;; a `method' which defines a meaning of an operator specific to its argument
;;; type (c.f. generic function and method of CLOS).  
;;; We construct one `method' object for each operator declaration, which 
;;; gathers the syntactical + semantical information of an operator specific to
;;; one arity, having the following informations:
;;;    operator: corresponding operator.
;;;    constructor : t iff the method is a constructor of sort `coarity'.
;;;    arity   : list arguments' sorts.
;;;    coarity : resulting sort of the operation.
;;;    rules-with-same-top : rewrite rules with both sides have the same top
;;;                          operator.
;;;    rules-with-different-top : rewrite rules with both sides have different
;;;                               top operator.
;;;    evaluator : evaluating function of the term having the operator as top.
;;;
;;; A method is placed on the `operator' part of terms of operator application
;;; form (including non-builtin constant terms) .
;;; Thus we can access most of the informations neccessary for rewriting in
;;; direct manner.
;;;

;;; ** NOTE *********************************************************************
;;; A method cannot be shared among modules, because importing module can define
;;; additional axioms for the method and possibly define other polymorphic
;;; operations. To enable the data be shared as far as possible, METHOD object
;;; itself contains only module INDEPENDENT informations of a method and some
;;; infos from operator (theory,etc.) for efficient rewriting process. 
;;; Module dependent parts (such as axioms, overloaded mehtods info) are stored
;;; in a table belonging to each module, and the module dependent info is
;;; accessed from the table (see "operator.lisp").
;;; *****************************************************************************

;;; * NOTE* The slots defined here are all module idependent.
#||
(defterm method (object)
  :visible (name			; operator name (canonicalized).
	    arity			; arity, list of argument sorts.
	    coarity)			; coarity
  :hidden (module			; the module it belongs.
	   constructor			; flag, t iff the method is a
					; constructor. not yet used.
	   supplied-strategy		; user supplied rewrite strategy.
	   form				; describes the form of a term with the
					; method as top. used for parsing.
	   precedence			; precedence used for parsing.
	   associativity		; associative info used for parsing.
	   memo				; t iff the rewriting will be memoized.
	   behavioural			; t iff the method is behavioural method.
	   coherent			; t iff the method is behaviourally coherent.
	   error			; t iff the method is error method and user
					; defined.
	   )
  :int-printer print-method-object
  :print print-method-internal)
||#

(defstruct (method (:include object (-type 'method))
		   (:constructor make-method)
		   (:constructor method* (name arity coarity))
		   (:copier nil)
		   (:print-function print-method-object))
  (name	nil :type list)			; operator name (canonicalized).
  (arity nil :type list)		; arity, list of argument sorts.
  (coarity nil :type (or null sort*))	; coarity
  (module nil :type (or null module))	; the module it belongs.
  (constructor nil :type (or null t))	; flag, t iff the method is a
					; constructor. not yet used.
  (supplied-strategy nil :type list)	; user supplied rewrite strategy.
  (form nil :type list)			; describes the form of a term with the
					; method as top. used for parsing.
  (precedence nil :type (or null fixnum))
					; precedence used for parsing.
  (associativity nil :type symbol)	; associative info used for parsing.
  (behavioural nil :type (or null t))	; t iff the method is behavioural method.
  ;; (coherent nil :type (or null t))	; t iff the method is behaviourally coherent.
  (error nil :type (or null t))		; t iff the method is error method and user
					; defined.
  (derived-from nil :type (or null method))
  (has-memo nil :type (or null t))
  (id-symbol nil :type symbol)
  )

(eval-when (eval load)
  (setf (symbol-function 'is-method) (symbol-function 'method-p))
  (setf (get 'method :type-predicate) (symbol-function 'method-p))
  (setf (get 'method :print) 'print-method-internal))

(defun print-method-object (obj stream &rest ignore)
  (declare (ignore ignore))
  (format stream "#<meth ~a : ~x>" (method-name obj) (addr-of obj)))

;;; Primitive constructor ------------------------------------------------------

;;; *NOTE*: assumes that the name is already canonicalized.
;;;
(defmacro create-operator-method (_name _arity _coarity)
  `(let ((meth (method* ,_name ,_arity ,_coarity)))
     (set-context-module meth)
     meth))

;;; Primitive type predicate ---------------------------------------------------

(defmacro operator-method-p (_o) `(is-method ,_o))

;;; Primitive accessors --------------------------------------------------------

;;; (defmacro method-name (_m) `(%method-name ,_m))
(defmacro method-symbol (_m) `(car (method-name ,_m)))
;;; (defmacro method-arity (_m) `(%method-arity ,_m))
;;; (defmacro method-coarity (_m) `(%method-coarity ,_m))
;;; (defmacro method-constructor (_m) `(%method-constructor ,_m))
;;; (defmacro method-form (_m) `(%method-form ,_m))
;;; (defmacro method-supplied-strategy (_m) `(%method-supplied-strategy ,_m))
;;; (defmacro method-precedence (_m) `(%method-precedence ,_m))
;;; (defmacro method-memo (_m) `(%method-memo ,_m))
;;; (defmacro method-module (_m) `(%method-module ,_m))
;;; (defmacro method-associativity (_m) `(%method-associativity ,_m))
;;; (defmacro method-behavioural (_m) `(%method-behavioural ,_m))
(defmacro method-is-behavioural (_m) `(method-behavioural ,_m)) ; synonym
;;; (defmacro method-is-coherent (_m) `(method-coherent ,_m))
(defmacro method-is-user-defined-error-method (_m)
  `(method-error ,_m))

(defmacro method-is-for-cr (_m)
  `(object-info ,_m :cr))

(defun method-is-derived-from (m)
  (let ((df (method-derived-from m)))
    (if df
	(or (method-is-derived-from df)
	    df)
	nil)))

;;; synonym
(defmacro method-is-constructor? (m)
  `(method-constructor ,m))
    
;;; method-is-meta-demod
(defmacro method-is-meta-demod (_m)
  `(object-info ,_m :meta-demod))

;;; PRIMITIVE CONSTRUCTOR OF A METHOD

;;; MAKE-OPERATOR-METHOD name arity coairty
;;; create an instance of method of name `name' with given arity and coarity.

;;; NOT USED NOW
;;; (defvar .operator-method-recycler. (make-hash-table :test #'equal))

(defun allocate-operator-method (name arity coarity)
  (declare (type list name)
	   (type list arity)
	   (type sort* coarity)
	   (values method))
  #||
  (let ((key (list name arity coarity)))
    (or (gethash key .operator-method-recycler.)
      (let ((meth (method* name arity coarity)))
	(setf (gethash key .operator-method-recycler.) meth)
	meth)))
  ||#
  (create-operator-method name arity coarity)
  )

(defun make-method-id-symbol (method)
  (let* ((nam (method-name method))
	 (mixfix (find-if #'(lambda (x) (string= x "_")) (car nam))))
    (if mixfix
	(intern (make-print-operator-id (car nam)))
	(intern (format nil "~a/~d"
			(make-print-operator-id (car nam))
			(cdr nam))))))

(defun make-operator-method (&key name arity coarity)
  (declare (type list name arity)
	   (type (or null sort*) coarity)
	   (values method))
  (let ((meth (allocate-operator-method name arity coarity)))
    (declare (type method meth))
    (setf (method-module meth) *current-module*
	  (method-constructor meth) nil
	  (method-supplied-strategy meth) nil
	  (method-precedence meth) nil
	  (method-associativity meth) nil
	  (method-id-symbol meth) (make-method-id-symbol meth))
    meth))

;;; EQUALITIES AMONG METHODS

;;; Logically equal if it belongs to the same operator, and has
;;; the same rank.
;;;
(defmacro method-equal (*__meth1 *__meth2)
  (once-only (*__meth1 *__meth2)
   `(and (eq (method-name ,*__meth1) (method-name ,*__meth2))
         (sort-list= (method-arity ,*__meth1) (method-arity ,*__meth2))
         (sort= (method-coarity ,*__meth1) (method-coarity ,*__meth2)))))

;;; The same object.
(defmacro method= (*_*meth1 *_*meth2) `(eq ,*_*meth1 ,*_*meth2))
(defun method-w= (m1 m2)
  (or (method= m1 m2)
      (when (and (sort= (method-coarity m1) *sort-id-sort*)
		 (sort= (method-coarity m2) *sort-id-sort*))
	(equal (method-symbol m1) (method-symbol m2)))))
	

;;; METHOD-IS-OF-SAME-OPERATOR : Method1 Method2 -> Bool
;;; Returns t iff the given two methods are of the same operator.
;;; NOTE: they are not neccessarily comparable in terms of their ranks.
;;;
(defmacro method-is-of-same-operator (*_*m1 *_*m2)
   `(eq (method-name ,*_*m1) (method-name ,*_*m2)))

(defmacro method-is-of-same-operator-safe (*_*m1 *_*m2)
   `(and (method-p ,*_*m2) (eq (method-name ,*_*m1) (method-name ,*_*m2))))

;;; this also checks that coarity is in same connected component
(defmacro method-is-of-same-operator+ (_m1 _m2)
  `(let ((ma ,_m1)
	 (mb ,_m2))
     (and (method-is-of-same-operator ma mb)
	  (is-in-same-connected-component (method-coarity ma)
					  (method-coarity mb)
					  (module-sort-order *current-module*)))))

;;; method-is-predicate
(defun method-is-predicate (method)
  (and (sort= *bool-sort* (method-coarity method))
       (not (member *bool-sort* (method-arity method)))
       (not (method= method *bool-true-meth*))
       (not (method= method *bool-false-meth*))
       ))

;;; METHOD ACCESSORS

(defun find-method-in-method-list (arity coarity method-list)
  (declare (type list arity method-list)
	   (type sort* coarity)
	   (values (or null method)))
  (let ((methods method-list))
    (dolist (m methods)
      (if (and (sort-list= arity (method-arity m))
	       (sort= coarity (method-coarity m)))
	  (return-from find-method-in-method-list m)))))

;;; ***********
;;; METHOD-INFO
;;; ***********
;;; Internal structure constaining module dependent infos of a method.
;;; does not appear explicitly in Chaos program.

#||
(defterm !method-info (int-object)	; (static-int-object) ; internal term.
  :hidden (operator                     ; pointer to the operator.
	   theory                       ; equational theory.
	   lower-methods		; list of lower comparable methods,
					; sorted lower->higher, exclusive.
	   overloaded-methods		; list of overloaded methods,
					; sortd higher->lower, exclusive.
	   rules-with-same-top		; rewrite rules with lhs and rhs have a
					; common top method.
	   rules-with-different-top	; rewrite rules with lhs and rhs have
					; different top method.
	   strictly-overloaded		; t iff the method is strictly
					; overloaded ,i.e., has no incomparable
					; overloaded method.
	   rew-strategy			; rewrite strategy.
	   has-trans			; flag, t iff the method has transitivity
					; axioms.
	   ))

||#

(defstruct (!method-info (:include object (-type '!method-info))
			 (:copier nil)
			 (:constructor make-!method-info)
			 (:constructor !method-info* nil)
			 (:print-function chaos-pr-object))
  (operator nil :type (or null operator))
					; pointer to the operator.
  (theory nil :type (or null op-theory)) ; equational theory.
  (lower-methods nil :type list)	; list of lower comparable methods,
					; sorted lower->higher, exclusive.
  (overloaded-methods nil :type list)	; list of overloaded methods,
					; sortd higher->lower, exclusive.
  (macros nil :type list)		; macro definitions
  (rules-with-same-top nil)		; rewrite rules with lhs and rhs have a
					; common top method.
  (rules-with-different-top nil :type list)
					; rewrite rules with lhs and rhs have
					; different top method.
  (strictly-overloaded nil :type (or null t))
					; t iff the method is strictly
					; overloaded ,i.e., has no incomparable
					; overloaded method.
  (rew-strategy	nil :type list)		; rewrite strategy.
  (has-trans nil :type (or null t))	; flag, t iff the method has transitivity
					; axioms.
  (theory-info-for-matching nil
			    :type (or null theory-info))
  (coherent nil :type (or null t))	; t iff behaviouraly coherent
  )

(eval-when (eval load)
  (setf (symbol-function 'is-!method-info) (symbol-function '!method-info-p))
  (setf (get '!method-info :type-predicate) (symbol-function '!method-info-p))
  (setf (get '!method-info :print) nil))
	
;;;
;;; GET-METHOD-INFO
;;;
#||
(defun get-method-info (method &optional (opinfo-table *current-opinfo-table*))
  (if (and (eq method .method1.) (eq opinfo-table .method-tab1.))
      .method-val1.
      (if (and (eq method .method2.) (eq opinfo-table .method-tab2.))
	  .method-val2.
	  (let ((res (gethash method opinfo-table)))
	    (if res
		(progn
		  (setq .method2. .method1.
			.method-tab2. .method-tab1.
			.method-val2. .method-val1.)
		  (setq .method1. method
			.method-tab1. opinfo-table
			.method-val1. res)
		  res)
		#||
		(with-output-chaos-error ()
		  (format t "context is inconsistent, could not get info for operator:")
		  (format t "~& ~a" (method-name method))
		  (chaos-to-top))
		||#
		nil
		)))))
||#

(declaim (inline get-method-info))

(#+GCL si::define-inline-function #-GCL defun
       get-method-info (method opinfo-table)
       (declare (type method method)
		(type (or null hash-table) opinfo-table)
		(values (or null !method-info)))
       (unless opinfo-table
	 (with-output-panic-message ()
	   (format t "get-method-info: no opinfo-table")
	   (chaos-error 'panic)))
       (gethash method opinfo-table))

(defsetf get-method-info (_method &optional (_opinfo-table
					    *current-opinfo-table*))
    (_val) 
  `(setf (gethash ,_method ,_opinfo-table) ,_val))

(defmacro method-operator (*-_m &optional (*-_info-table '*current-opinfo-table*))
  `(!method-info-operator (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-theory (*-_m &optional (*-_info-table '*current-opinfo-table*))
  `(!method-info-theory (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-theory-info-for-matching
    (*_m &optional (*_info-table '*current-opinfo-table*))
  ` (!method-info-theory-info-for-matching
     (get-method-info ,*_m ,*_info-table)))

(defmacro method-lower-methods (*-_m &optional (*-_info-table
						'*current-opinfo-table*)) 
  `(!method-info-lower-methods (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-overloaded-methods (*-_m &optional (*-_info-table
						     '*current-opinfo-table*)) 
  `(!method-info-overloaded-methods (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-rules-with-same-top (*-_m &optional (*-_info-table
						      '*current-opinfo-table*)) 
  `(!method-info-rules-with-same-top (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-rules-with-different-top (*-_m &optional (*-_info-table
							   '*current-opinfo-table*))  
  `(!method-info-rules-with-different-top (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-macros (*_ms &optional (_info_table '*current-opinfo-table*))
  `(!method-info-macros (get-method-info ,*_ms ,_info_table)))

;;; synonym
(defmacro method-rules (_m &optional (_info-table '*current-opinfo-table*))
  `(!method-info-rules-with-different-top (get-method-info ,_m ,_info-table)))

(defmacro method-strictly-overloaded (*-_m &optional (*-_info-table
						      '*current-opinfo-table*))
  `(!method-info-strictly-overloaded (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-rew-strategy (*-_m &optional (*-_info-table '*current-opinfo-table*))
  `(!method-info-rew-strategy (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-rewrite-strategy (*-_m &optional (*-_info-table
						   '*current-opinfo-table*))
  `(!method-info-rew-strategy (get-method-info ,*-_m ,*-_info-table)))

(defmacro method-has-trans-rule (_m &optional (_info-table
					       '*current-opinfo-table*))
  `(!method-info-has-trans (get-method-info ,_m ,_info-table)))

(defmacro method-is-coherent (_m &optional (_info-table
					    '*current-opinfo-table*))
  `(!method-info-coherent (get-method-info ,_m ,_info-table)))

;;; synonym..
(defmacro method-coherent (_m &optional (_info-table
					    '*current-opinfo-table*))
  `(!method-info-coherent (get-method-info ,_m ,_info-table)))

;;; CONSTRUCTOR ----------------------------------------------------------------

#||
(defvar .method-info-recycler. (make-hash-table :test #'equal))
(defun allocate-method-info (method module)
  (let* ((key (list method module))
	 (minfo (gethash key .method-info-recycler.)))
    (if minfo
	minfo
	(progn
	  (setq minfo (!method-info*))
	  (when (modexp-is-simple-name (module-name module))
	    (setf (gethash key .method-info-recycler.) minfo))
	  minfo))))
||#

(defun allocate-method-info (meth mod)
  (declare (ignore meth mod)
	   (values !method-info))
  (make-!method-info))

(defun make-method-info (method module operator)
  (declare (type method method)
	   (type module module)
	   (type operator operator)
	   (values !method-info))
  (let ((info (allocate-method-info method module)))
    (setf (!method-info-operator info) operator
	  (!method-info-theory info) nil
	  (!method-info-lower-methods info) nil
	  (!method-info-overloaded-methods info) nil)
    (unless (!method-info-rules-with-same-top info)
      (setf (!method-info-rules-with-same-top info) (create-rule-ring nil)))
    (setf (!method-info-rules-with-different-top info) nil
	  (!method-info-strictly-overloaded info) nil)
    info))

;;; Little Utils --------------------------------------------------------------

;;;
;;; METHOD-THEORY-INFO-FOR-MATCHING
;;;
#||
(defun method-theory-info-for-matching (method &optional (info-table
							  *current-opinfo-table*)) 
  (declare (type method method)
	   (type hash-table info-table)
	   (values theory-info))
  (let* ((th (method-theory method info-table))
	 (info (theory-info th)))
    (declare (type op-theory th)
	     (type theory-info info))
    (if (zero-rule-only th)
	(%svref *theory-info-array*
		(logandc2 (the fixnum (theory-info-code info)) .Z.))
	info)))
||#

(defun compute-method-theory-info-for-matching (method &optional
						       (info-table
							*current-opinfo-table*))
  (declare (type method method)
	   (type hash-table info-table))
  (let ((res nil))
    (let* ((th (method-theory method info-table))
	 (info (theory-info th)))
    (declare (type op-theory th)
	     (type theory-info info))
    (setq res
	  (if (zero-rule-only th)
	      (%svref *theory-info-array*
		      (logandc2 (the fixnum (theory-info-code info)) .Z.))
	      info))
    (setf (method-theory-info-for-matching method info-table)
	  res)
    )))

;;; GET-METHOD-PRECEDENCE
;;;
(defun get-method-precedence (method &optional
				     (method-info-tab *current-opinfo-table*))
  (declare (type method method)
	   (type hash-table method-info-tab)
	   (values fixnum))
  (or (the (or null fixnum) (method-precedence method))
      (the (or null fixnum) (operator-computed-precedence
			     (method-operator method method-info-tab)))
      (the (or null fixnum) (operator-precedence
			     (method-operator method method-info-tab)))
      (compute-operator-precedence (method-operator method method-info-tab))))

;;; *** The following default precedence must be determined later again ***
;;;
(defparameter .default-prec. 41)
(defparameter .default-unary-prec. 15)

(defun compute-operator-precedence (operator)
  (declare (type operator operator)
	   (values fixnum))
  (let ((given-prec (operator-precedence operator))
	(token-seq (operator-token-sequence operator))
	(is-standard (not (operator-is-mixfix operator))))
    (declare (type (or null fixnum) given-prec)
	     (type list token-seq)
	     (type (or null t) is-standard))
    (if given-prec
	given-prec
	(if is-standard
	    0
	    (if (and (not (eq t (car token-seq)))
		     (not (eq t (car (last token-seq)))))
		;; not of the pattern "_ args-or-keyword... _ "
		0
		(if (and (eq t (car (last token-seq)))
			 (not (memq t (butlast token-seq))))
		    ;; unary operator.
		    .default-unary-prec.
		    ;; others.
		    .default-prec.))))))

;;; *********
;;; RULE-RING
;;; *********

;;; Based on the implementation of OBJ3.
;;; Used for holding rewrite rules with the same top operator on the both sides.
;;;
;; A ring of rules is represented by a circular list with 2 pointers, one for
;; the next rule to be returned and one for the last rule which has been
;; successfuly apply. 
;; Be careful for printing! (and debugging)

(defstruct (rule-ring (:copier nil))
  (ring nil :type list)			; the circular list of rules
  (current nil :type list)		; current position
  (mark nil :type list))		; end mark

;;;  0 : ring
;;;  1 : current
;;;  2 : mark

;;; (defmacro rule-ring-ring (r) `(object-typer 0))
;;; (defmacro rule-ring-current (r) `(t-ref ,r 1))
;;; (defmacro rule-ring-mark (r) `(t-ref ,r 2))
;;;
;;; (defun make-rule-ring (&key ring current mark)
;;;   (let ((r (alloc-term 3)))
;;;     (setf (rule-ring-ring r) ring
;;; 	  (rule-ring-current r) current
;;; 	  (rule-ring-mark r) mark)
;;;    r))

;;; CREATE-RULE-RING list-of-rules
;;; creates new rule-ring intialized with given rules.
;;; if given rules are empty a empty ring is created.
;;;
(defun create-rule-ring (list-of-rules)
  (declare (type list list-of-rules)
	   (values rule-ring))
  (if list-of-rules
      (make-rule-ring :ring (rplacd (last list-of-rules) list-of-rules)
		      :current list-of-rules
		      :mark list-of-rules)
      (make-rule-ring)))

;;; ADD-RULE-TO-RING rule-ring rule
;;; add a new rule with same top in the rule ring which is modified.
;;;
(defun add-rule-to-ring (rring rule)
  (declare (type rule-ring rring)
	   (type t rule))
  (let ((ring (rule-ring-ring rring)))
    (if ring
	;; add the rule to tail.
	(rplacd ring (push rule (cdr ring)))
	;; no ring.
        (let ((new-ring (list rule)))
	  (setf (rule-ring-ring rring) (rplacd new-ring new-ring))))))

;;; INITIALIZE-RULE-RING rule-ring
;;; initialize a rule-ring, that is put the current and mark pointers
;;; at the "beginning of the list". Returns the rule under current.
;;
(declaim (inline initialize-rule-ring))
#+GCL
(si::define-inline-function initialize-rule-ring (rr)
  (setf (rule-ring-current rr) (rule-ring-ring rr))
  (setf (rule-ring-mark rr) nil)
  (car (rule-ring-current rr)))

#-GCL
(defun initialize-rule-ring (rr)
  (declare (type rule-ring rr)
	   (values t))
  (setf (rule-ring-current rr) (rule-ring-ring rr))
  (setf (rule-ring-mark rr) nil)
  (car (rule-ring-current rr))
  )


;;; RULE-RING-SET-MARK rule-ring
;;; set the mark to the current rule.
;;;
(declaim (inline rule-ring-set-mark))
#+GCL
(si::define-inline-function rule-ring-set-mark (rr)
  (setf (rule-ring-mark rr) (rule-ring-current rr)))
#-GCL
(defun rule-ring-set-mark (rr)
  (declare (type rule-ring rr)
	   (values list))
  (setf (rule-ring-mark rr) (rule-ring-current rr)))

;;; RULE-RING-NEXT rule-ring
;;;  returns the next rule in the ring rule
;;;
(declaim (inline rule-ring-next))
#+GCL
(si::define-inline-function rule-ring-next (rr)
  (unless (rule-ring-mark rr) (rule-ring-set-mark rr))
  ;; update the current pointer
  (let ((rules (cdr (rule-ring-current rr))))
    (setf (rule-ring-current rr) rules)
    (car rules))
  )
#-GCL
(defun rule-ring-next (rr)
  (declare (type rule-ring rr)
	   (values list))
  (unless (rule-ring-mark rr) (rule-ring-set-mark rr))
  ;; update the current pointer
  (let ((rules (cdr (rule-ring-current rr))))
    (setf (rule-ring-current rr) rules)
    (car rules))
  )

;;; END-OF-RULE-RING rule-ring
;;; returns true iff it is the end, i.e. iff no more rule of the ring
;;; can be apply, that is iff current and mark are the same.
;;;
(declaim (inline end-of-rule-ring))
#+GCL
(si::define-inline-function end-of-rule-ring (rr)
  (eq (rule-ring-current rr) (rule-ring-mark rr)))
#-GCL
(defun END-OF-RULE-RING (rr)
  (declare (type rule-ring rr)
	   (values (or null t)))
  (eq (rule-ring-current rr) (rule-ring-mark rr)))

;;; RULE-RING-IS-EMPTY rule-ring
;;;
(declaim (inline rule-ring-is-empty))
#+GCL
(si::define-inline-function rule-ring-is-empty (rr)
  (null (rule-ring-ring rr)))
#-GCL
(defun rule-ring-is-empty (rr)
  (declare (type rule-ring rr)
	   (values (or null t)))
  (null (rule-ring-ring rr)))

;;; RULE-RING-TO-LIST rule-ring
;;;
(declaim (inline rule-ring-to-list))
#+GCL
(si::define-inline-function rule-ring-to-list (rr)
  (let ((list nil))
    (do ((rule (initialize-rule-ring rr) (rule-ring-next rr)))
	((end-of-rule-ring rr))
	(push rule list))
    list))
#-GCL
(defun rule-ring-to-list (rr)
  (declare (type rule-ring rr)
	   (values list))
  (let ((list nil))
    (do ((rule (initialize-rule-ring rr) (rule-ring-next rr)))
	((end-of-rule-ring rr))
	(push rule list))
    list))

;;; COPY-RULE-RING rule-ring
;;;
(defun copy-rule-ring (rule-ring)
  (declare (type rule-ring rule-ring)
	   (values rule-ring))
  (let ((ring (rule-ring-ring rule-ring)))
    (make-rule-ring :ring ring
		    :current ring
		    :mark nil)))


;;; ****************
;;; METHOD-UTILITIES
;;; ****************

;;; METHOD-IS-ERROR-METHOD : Method -> Bool
;;;

(defun method-is-error-method (method)
  (declare (type method method)
	   (values (or null t)))
  (let ((coar (method-coarity method)))
    (or (err-sort-p coar)
	(dolist (a (method-arity method) nil)
	  (if (err-sort-p a)
	      (return-from method-is-error-method t))))))

#||
(defun method-is-universal (method)
  (and (method-arity method)
       (every #'(lambda (x) (or (sort= x *universal-sort*)
				(sort= x *huniversal-sort*)
				(sort= x *cosmos*)))
	      (method-arity method))))
||#

(defun method-is-universal (method)
  (declare (type method method)
	   (values (or null t)))
  (let ((arity (method-arity method)))
    (declare (type list arity))
    (and arity
	 (dolist (ar arity t)
	   (declare (type sort* ar))
	   (unless (or (sort= ar *universal-sort*)
		       (sort= ar *huniversal-sort*)
		       (sort= ar *cosmos*))
	     (return-from method-is-universal nil))))))

(defun method-is-universal* (method)
  (declare (type method method)
	   (values (or null t)))
  (let ((arity (method-arity method)))
    (declare (type list arity))
    (and arity
	 (dolist (ar arity nil)
	   (declare (type sort* ar))
	   (when (or (sort= ar *universal-sort*)
		     (sort= ar *huniversal-sort*)
		     (sort= ar *cosmos*))
	     (return-from method-is-universal* t))))))

;;; METHOD-IS-ASSOCIATIVE : Method -> Bool
;;; non-nil iff the methods equational theory contains associativity.
;;;
(defun method-is-associative (meth &optional (info *current-opinfo-table*))
  (declare (type method meth)
	   (type hash-table info)
	   (values (or null t)))
  (theory-contains-associativity (method-theory meth info)))

;;; METHOD-IS-IDENTITY
;;; non-nil iff the method's equational theory contains ideitity.
;;;
(defun method-is-identity (meth &optional (info *current-opinfo-table*))
  (declare (type method meth)
	   (type hash-table info)
	   (values (or null t)))
  (theory-contains-identity (method-theory meth info)))

;;; METHOD-IS-COMMUTATIVE
;;; non-nil iff the method's equational theory contains commutativity.
;;;
(defun method-is-commutative (meth &optional (info *current-opinfo-table*))
  (declare (type method meth)
	   (type hash-table info)
	   (values (or null t)))
  (theory-contains-commutativity (method-theory meth info)))
  
;;; METHOD-IS-IDEMPOTENT
;;;
(defun method-is-idempotent (meth &optional (info *current-opinfo-table*))
  (declare (type method meth)
	   (type hash-table info)
	   (values (or null t)))
  (theory-contains-idempotency (method-theory meth info)))

;;; METHOD-IS-OVERLOADED-WITH : Method Method SORT-ORDER -> Bool
;;; Returns t iff the given two methods are comparable, ie, they are of the same
;;; operator, and their ranks are ordered.
;;;

(defun method-is-overloaded-with (meth1 meth2 &optional (so *current-sort-order*))
  (declare (type method meth1 meth2)
	   (type sort-order so)
	   (values (or null t)))
  (and (method-is-of-same-operator meth1 meth2)
       (let ((arx (method-arity meth1))
	     (ary (method-arity meth2))
	     (coarx (method-coarity meth1))
	     (coary (method-coarity meth2)))
	 (declare (type list arx ary)
		  (type sort* coarx coary))
	 (or (and (sort<= coarx coary so)
		  (sort-list<= arx ary so))
	     (and (sort<= coary coarx so)
		  (sort-list<= ary arx so))))))

;;; METHOD-IS-IN-SAME-COMPONENT : Method1 Method2 -> Bool
;;; Returns t iff two methods are of the same operator, have arities which
;;; are pair-wise being in the connected component, and coarities are also in
;;; the connected component.
;;;
;;; * NOTE * assumes err sorts are already generated.
;;;
(defun method-is-in-same-component (meth1 meth2 &optional (so *current-sort-order*))
  (declare (type method meth1 meth2)
	   (type sort-order so)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (and (method-is-of-same-operator meth1 meth2)
	   (is-in-same-connected-component
	    (method-coarity meth1) (method-coarity meth2) so)
	   (let ((al1 (method-arity meth1))
		 (al2 (method-arity meth2)))
	     (loop (if (null al1) (return t))
		   (unless (is-in-same-connected-component (car al1) (car al2) so)
		     (return nil))
		   (setf al1 (cdr al1)
			 al2 (cdr al2)))))))

;;; METHOD-IS-INSTANCE-OF method-1 method2 sort-order
;;; condition: of same operator, larger coarity; smaller arity smaller coarity too.
;;;
(defun method-is-instance-of (meth1 meth2 sort-order)
  (declare (type method meth1 meth2)
	   (type sort-order sort-order)
	   (values (or null t)))
  (and (method-is-of-same-operator meth1 meth2)
       (or (method-is-universal* meth2)
	   (and (or (not (sort= (method-coarity meth1) (method-coarity meth2)))
		    (not (sort-list= (method-arity meth1) (method-arity meth2))))
		(sort<= (method-coarity meth1) (method-coarity meth2) sort-order)
		(sort-list<= (method-arity meth1) (method-arity meth2) sort-order)))))

;;; METHOD-IS-SAME-QUAL-METHOD : Method1 Method2 -> Bool
;;;
(defun method-is-same-qual-method (meth1 meth2)
  (declare (type method meth1 meth2)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (and (method-is-of-same-operator meth1 meth2)
	   (is-in-same-connected-component* (method-coarity meth1)
					    (method-coarity meth2)
					    *current-sort-order*))))

;;; METHOD<= : Method1 Method2 -> Bool
;;; returns t iff
;;;  (1) the given method is the different overloaded ones
;;;  (2) arity of method1 <= method2
;;;  (3) coarity of method1 <= method2
;;;
(defun method<= (meth1 meth2 &optional (so *current-sort-order*))
  (declare (type method meth1 meth2)
	   (type sort-order so)
	   (values (or null t)))
  (and (method-is-of-same-operator meth1 meth2)
       (not (eq meth1 meth2))
       (and (sort<= (method-coarity meth1) (method-coarity meth2) so)
	    (sort-list<= (method-arity meth1) (method-arity meth2) so))))

;;; METHOD-IS-RESTRICTION-OF : Method1 Method2 -> Bool
;;; just the same as method<=
;;;
(defun method-is-restriction-of (meth1 meth2 &optional (so *current-sort-order*))
  (declare (type method meth1 meth2)
	   (type sort-order so)
	   (values (or null t)))
  (and (method-is-of-same-operator meth1 meth2)
       (not (eq meth1 meth2))
       (or (method-is-universal* meth2)
	   (and (sort<= (method-coarity meth1) (method-coarity meth2) so)
		(sort-list<= (method-arity meth1) (method-arity meth2) so)))))

;;; METHOD-IS-ASSOCIATIVE-RESTRICTION-OF : Method1 Method2 -> Bool
;;; returns t iff
;;; (1) methods are overloaded and associative,
;;; (2) Method1 <= Method2
;;;
;;; *NOTE* second method is assumed to be just associative.
;;;
#-GCL (declaim (inline method-is-associative-restriction-of))
#||
(defun method-is-associative-restriction-of (meth1
					     meth2
					     &optional
					     (so *current-sort-order*)
					     (info *current-opinfo-table*))
  (declare (type method meth1 meth2)
	   (type sort-order so)
	   (type hash-table info)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (and (eq (method-name meth1) (method-name meth2))
	   (sort<= (method-coarity meth1)
		   (method-coarity meth2)
		   so)
	   (sort-list<= (method-arity meth1)
			(method-arity meth2)
			so)
	   (theory-contains-associativity (method-theory meth1 info)))))
||#
#-GCL
(defun method-is-associative-restriction-of (meth1
					     meth2)
  (declare (type method meth1 meth2)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (equal (method-name meth1) (method-name meth2))))

#+GCL 
(si:define-inline-function  method-is-associative-restriction-of (meth1
					     meth2)
  (declare (type method meth1 meth2)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (eq (method-name meth1) (method-name meth2))))

;;; METHOD-IS-AC-RESTRICTION-OF : Method1 Method2 -> Bool
;;; returns t iff
;;; (1) methods are overloaded and have theory AC
;;; (2) Method1 <= Method2
;;;
;;; *NOTE* second method is assumed to be associative-commutive.
;;;
#||
(defun method-is-AC-restriction-of (meth1
				    meth2
				    &optional
				    (so *current-sort-order*)
				    (info *current-opinfo-table*))
  (declare (type method meth1 meth2)
	   (type sort-order so)
	   (type hash-table info)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (and (eq (method-name meth1) (method-name meth2))
	   (sort<= (method-coarity meth1)
		   (method-coarity meth2)
		   so)
	   (sort-list<= (method-arity meth1)
			(method-arity meth2)
			so)
	   (theory-contains-AC (method-theory meth1 info)))))
||#

#-GCL (declaim (inline method-is-ac-restriction-of))

#-GCL
(defun method-is-AC-restriction-of (meth1
				    meth2
				    &rest ignore)
  (declare (type method meth1 meth2)
	   (ignore ignore)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (eq (method-name meth1) (method-name meth2))))

#+GCL
(si:define-inline-function
    method-is-ac-restriction-of (meth1 meth2)
  (or (method= meth1 meth2)
      (eq (method-name meth1) (method-name meth2))))
					     

;;; METHOD-IS-COMMUTATIVE-RESTRICTION-OF : Method1 Method2 -> Bool
;;; returns t iff
;;; (1) methods are overloaded and have theory C
;;; (2) Method1 <= Method2
;;;
;;; *NOTE* second method is assumed to be just commutive.
;;;
#||
(defun method-is-commutative-restriction-of (meth1
					     meth2
					     &optional
					     (so *current-sort-order*)
					     (info *current-opinfo-table*))
  (declare (type method meth1 meth2)
	   (type sort-order so)
	   (type hash-table info)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (and (eq (method-name meth1) (method-name meth2))
	   (sort<= (method-coarity meth1)
		   (method-coarity meth2)
		   so)
	   (sort-list<= (method-arity meth1)
			(method-arity meth2)
			so)
	   (theory-contains-commutativity (method-theory meth1 info)))))
||#

#-GCL (declaim (inline method-is-commutative-restriction-of))

#-GCL
(defun method-is-commutative-restriction-of (meth1 meth2)
  (declare (type method meth1 meth2)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (eq (method-name meth1) (method-name meth2))))

#+GCL
(si:define-inline-function method-is-commutative-restriction-of (meth1 meth2)
  (declare (type method meth1 meth2)
	   (values (or null t)))
  (or (method= meth1 meth2)
      (eq (method-name meth1) (method-name meth2))))

;;; METHOD-IS-OVERLOADED-WITH-AC-ATTRIBUTE : Method1 Method2 -> Bool
;;; returns t iff
;;; (1) method is Associative,
;;; (2) exists same name with AC then yes
;;;
(defun method-is-overloaded-with-AC-attribute (meth
					       &optional
					       (opinfo-table
						*current-opinfo-table*))
  (declare (type method meth)
	   (type hash-table opinfo-table)
	   (values (or null t)))
  (dolist (meth2 (method-overloaded-methods meth opinfo-table))
    (declare (type method meth2))
    (when (and (not (method= meth meth2))
	       (eq (method-name meth) (method-name meth2))
	       (theory-contains-AC (method-theory meth2 opinfo-table)))
      (return t))))

;;; GREATEST-AC-METHOD-LESS-THAN : Method -> Method
;;; Theory is AC and satisfies the above condition.
;;;
(defun greatest-AC-method-less-than (meth
				     &optional
				     (opinfo-table *current-opinfo-table*))
  (declare (type method meth)
	   (type hash-table opinfo-table)
	   (values list))
  (let ((res nil))
    (dolist (meth2 (method-overloaded-methods meth opinfo-table))
      (declare (type method meth2))
      (when (and (not (method= meth meth2))
		 (method-is-ac-restriction-of meth2 meth))
	(setq res meth2)))
    res))

;;; LIST-ASSOCIATIVE-METHOD-ABOVE : Method -> List[Method]
;;; * NOTE * assume default attribute values are already copied from operators
;;; to their methods.
;;; 
(defun list-associative-method-above (method &optional
					     (so *current-sort-order*)
					     (info-table *current-opinfo-table*))
  (declare (type method method)
	   (type sort-order so)
	   (hash-table info-table)
	   (values list))
  (let ((res nil)
	(coar (method-coarity method)))
    (declare (type sort* coar))
    (dolist (m (method-overloaded-methods method info-table))
      (declare (type method m))
      (when (and (not (method= m method))
		 ;; (not (method-is-error-method m))
		 ;; was (method-is-of-same-operator m method)
		 (eq (method-name m)
		     (method-name method))
		 (sort<= coar (method-coarity m) so)
		 (theory-contains-associativity (method-theory m info-table)))
	(push m res)))
    res))

;;; HIGHEST-METHODS-BELOW : Method Sort -> List[Method]
;;; returns the list of methods with the following properties:
;;; (1) has the lower or equal coarity to given method
;;; (2) has greater or equal coarity to given sort
;;;
(defun highest-methods-below (method sort
				     &optional
				     (so *current-sort-order*)
				     (opinfo-table *current-opinfo-table*))
  (declare (type method method)
	   (type sort* sort)
	   (type sort-order so)
	   (type hash-table opinfo-table)
	   (values list))
  (let ((methods (reverse (method-overloaded-methods method opinfo-table)))
	(res nil))
    (dolist (m methods)
      (declare (type method m))
      (when (sort<= (method-coarity m) sort so)
	(unless (dolist (m2 methods nil)
		  (when (and (not (method= m m2))
			     (sort<= (method-coarity m)
				     (method-coarity m2) so)
			     (sort<= (method-coarity m2) sort so)
			     (method<= m m2 so))
		    (return t)))
	  (push m res))))
    res))


;;; ******************************************
;;; UTIL PROCS MANIPULATING OVERLOADED METHODS
;;; ******************************************

;;; GET-DEFAULT-METHODS op &optional (module *current-module*)

(defun get-default-methods (op &optional (module *current-module*))
  (declare (type operator op)
	   (type module module)
	   (values list))
  (let ((gms nil))
    (dolist (m (operator-methods op (module-all-operators module)))
      (if (or (method-is-error-method m)
	      (method-is-universal m))
	  (push m gms)))
    gms))

;;; LOWEST-METHOD-DIRECT

(defun lowest-method-direct (method lower-bounds &optional (mod *current-module*))
  (declare (type method method)
	   (type list lower-bounds)
	   (type module mod)
	   (values method))
  (let ((*current-opinfo-table* (module-opinfo-table mod))
	(*current-sort-order* (module-sort-order mod))
	(cur-arity (method-arity method))
	(cur-coarity (method-coarity method))
	(res method))
    (declare (type hash-table *current-opinfo-table*
		   *current-sort-order*)
	     (type list cur-arity)
	     (type sort* cur-coarity))
    (dolist (meth (operator-methods (method-operator method)
				    (module-all-operators mod)))
      (declare (type method meth))
      (let ((new-coarity (method-coarity meth))
	    (new-arity (method-arity meth)))
	(declare (type sort* new-coarity)
		 (type list new-arity))
	(when (and (sort<= new-coarity cur-coarity)
		   (sort-list<= lower-bounds new-arity)
		   (sort-list<= new-arity cur-arity))
	  (setq res meth
		cur-coarity new-coarity
		cur-arity new-arity))))
    res))


;;; HIGHEST-METHOD-DIRECT

(defun highest-method-direct (method upper-bound
				     &optional (module *current-module*))
  (declare (type method method)
	   (type sort* upper-bound)
	   (type module module)
	   (values method))
  (let* ((*current-opinfo-table* (module-opinfo-table module))
	 (*current-sort-order* (module-sort-order module))
	 (elingible-flag (sort<= (method-coarity method) upper-bound))
	 (res (if elingible-flag method nil))
	 (cur-arity (if elingible-flag (method-arity method) nil))
	 (cur-coarity (if elingible-flag (method-coarity method) nil)))
    (declare (type hash-table *current-opinfo-table*
		   *current-sort-order*)
	     (type (or null t) elingible-flag)
	     (type list cur-arity)
	     (type (or null sort*) cur-coarity))
    (dolist (meth (operator-methods (method-operator method)
				    (module-all-operators module)))
      (declare (type method meth))
      (let ((new-arity (method-arity meth))
	    (new-coarity (method-coarity meth)))
	(when (and (sort<= new-coarity upper-bound)
		   (or (null res)
		       (and (sort<= cur-coarity new-coarity)
			    (sort-list<= cur-arity new-arity))))
	  (setf res meth  cur-coarity new-coarity  cur-arity new-arity))))
    res))


;;; STRICT-LOWER-COARITIES-DIRECT

(defun strict-lower-coarities-direct (method &optional (module *current-module*))
  (declare (type method method)
	   (type module module)
	   (values list))
  (let (;; (arity (method-arity method))
	(coarity (method-coarity method))
	(*current-opinfo-table* (module-opinfo-table module))
	(*current-sort-order* (module-sort-order module))
	(res nil))
    (declare (type sort* coarity)
	     (type hash-table *current-opinfo-table*
		   *current-sort-order*))
    (dolist (meth (operator-methods (method-operator method)
				    (module-all-operators module)))
      (declare (type method meth))
      (let ((new-coarity (method-coarity meth)))
	(declare (type sort* new-coarity))
	(when (and (not (member new-coarity res :test #'eq))
		   (sort< (method-coarity meth) coarity)
		   ;; (sort-list (method-arity meth) arity)
		   ;; this test is not needed by co-regularity.
		   )
	  (push new-coarity res))))
    res))


;;; LOWEST-METHOD
(defvar *op-debug* nil)

(defun lowest-method (method lower-bound &optional (module *current-module*))
  (declare (type method method)
	   (type list lower-bound)
	   (type module module)
	   (values method))
  (let ((*current-sort-order* (module-sort-order module))
	(*current-opinfo-table* (module-opinfo-table module)))
    (declare (type hash-table *current-sort-order* *current-opinfo-table*))
    (let ((over-methods (method-overloaded-methods method
						   (module-opinfo-table module))))
      (declare (type list over-methods))
      (when *op-debug*
	(format t "~&* lowest-method : given arity =")
	(dolist (s (method-arity method))
	  (princ " ")
	  (print-sort-name s))
	(princ ", coarity = ")
	(print-sort-name (method-coarity method))
	(format t "~&* lowest-method : lower-bound =")
	(dolist (s lower-bound)
	  (terpri)
	  (princ "   ")
	  (print-sort-name s))
	(format t "~%* lowest-method : over-methods =")
	(dolist (m over-methods)
	  (terpri)
	  (princ "    ")
	  (print-chaos-object m)))
      (when over-methods
	(dolist (meth over-methods)
	  (declare (type method meth))
	  (when (sort-list<= lower-bound (method-arity meth))
	    (when *op-debug*
	      (format t "~%lowest-method res=")
	      (print-chaos-object meth)
	      )
	    (return-from lowest-method meth))))
      (when *op-debug*
	(format t "~%lowest-method res=")
	(print-chaos-object method)
	)
      method)))

(defun lowest-method! (method lower-bound &optional (module *current-module*))
  (declare (type method method)
	   (type list lower-bound)
	   (type module module)
	   (values (or null method)))
  (flet ((select-one-method (method-list)
	   ;; select arbitrary one if every has the same rank
	   (let* ((cand (car method-list))
		  (coar (method-coarity cand))
		  (arity (method-arity cand)))
	     (dolist (m (cdr method-list) cand)
	       (unless (sort= coar (method-coarity m))
		 (return-from select-one-method nil))
	       (unless (sort-list= arity (method-arity m))
		 (return-from select-one-method nil))))))
    (let ((*current-sort-order* (module-sort-order module))
	  (*current-opinfo-table* (module-opinfo-table module))
	  (res nil))
      (declare (type hash-table *current-sort-order* *current-opinfo-table*))
      (let ((over-methods (method-overloaded-methods
			   method
			   (module-opinfo-table module))))

	(declare (type list over-methods))
	(when *on-debug*
	  (format t "~%* lowest-method! : over-methods =")
	  (dolist (m over-methods)
	    (terpri)
	    (princ "    ")
	    (print-chaos-object m)))
	;;
	(if over-methods
	    (progn
	      (dolist (meth over-methods)
		(declare (type method meth))
		(when (and (sort-list<= lower-bound (method-arity meth))
			   (not (member
				 meth
				 res
				 :test #'(lambda (x y)
					   (method-is-instance-of y
								  x
								  *current-sort-order*)))
				))
		  (push meth res)))
	      (when *on-debug*
		(format t "~%lowest-method! res=")
		(print-chaos-object res)
		)
	      (if (cdr res)
		  ;; was method
		  (or (select-one-method res)
		      method)
		  (car res)))
	    (return-from lowest-method! method))))))

(defun lowest-method* (method &optional lower-bound (module *current-module*))
  (declare (type method method)
	   (type list lower-bound)
	   (type module module)
	   (values (or null method)))
  (let* ((*current-sort-order* (module-sort-order module))
	 (*current-opinfo-table* (module-opinfo-table module))
	 (over-methods (method-overloaded-methods method
						  (module-opinfo-table module))))
    (declare (type hash-table *current-sort-order* *current-opinfo-table*)
	     (type list over-methods))
    (if over-methods
	(let ((*current-sort-order* (module-sort-order module))
	      (*current-opinfo-table* (module-opinfo-table module))
	      (cur-coarity (method-coarity method))
	      (cur-arity (method-arity method)))
	  (declare (type sort* cur-coarity)
		   (type list cur-arity))
	  (dolist (meth over-methods)
	    (declare (type method meth))
	    (let ((new-coarity (method-coarity meth))
		  (new-arity (method-arity meth)))
	      (declare (type sort* new-coarity)
		       (type list new-arity))
	      (when (and (sort<= new-coarity cur-coarity)
			 (if lower-bound
			     (sort-list<= lower-bound new-arity)
			   t)
			 (sort-list<= new-arity cur-arity))
		(return-from lowest-method* meth))))
	  method)
	method)))

;;; HIGHEST-METHOD
;;; NOTE assume overloaded-methods is sorted .lower => higher.
;;;
(defun highest-method (method &optional
			      upper-bound
			      (module *current-module*))
  (declare (type method method)
	   (type (or null sort*) upper-bound)
	   (type module module)
	   (values method))
  ;; (format t "~&highest-method : given method ")
  ;;  (print-chaos-object method)
  (let ((overloaded-methods
	 (reverse (method-overloaded-methods method
					     (module-opinfo-table module)))))
    (declare (type list overloaded-methods))
    (if (null (cdr overloaded-methods))
	(if overloaded-methods
	    (car overloaded-methods)
	    method)
	(let* ((*current-sort-order* (module-sort-order module))
	       (*current-opinfo-table* (module-opinfo-table module))
	       (eligible-flag (if upper-bound
				  (sort<= (method-coarity method) upper-bound)
				  t))
	       (method-res (if eligible-flag method nil))
	       (cur-arity (if eligible-flag (method-arity method) nil))
	       (cur-coarity (if eligible-flag (method-coarity method) nil)))
	  (declare (type hash-table *current-sort-order*
			 *current-opinfo-table*)
		   (type (or null t) eligible-flag)
		   (type list cur-arity)
		   (type (or null method) method-res)
		   (type (or null sort*) cur-coarity))
	  (dolist (meth (operator-methods (method-operator method)
					  (module-all-operators module))
		   method-res)
	    (declare (type method meth))
	    (let ((new-arity (method-arity meth))
		  (new-coarity (method-coarity meth)))
	      (declare (type list new-arity)
		       (type sort* new-coarity))
	      (when (and (if upper-bound
			     (sort<= new-coarity upper-bound)
			     t)
			 (or (null method-res)
			     (and (sort<= cur-coarity new-coarity)
				  (sort-list<= cur-arity new-arity))))
		(return meth))))))))

;;; GET-STRICT-LOWER-COARITIES : method module -> List[Sort]
;;;
(defun get-strict-lower-coarities (method &optional (module *current-module*))
  (declare (type method method)
	   (type module module)
	   (values list))
  (let* (;; (arity (method-arity method))
	 (coarity (method-coarity method))
	 (*current-sort-order* (module-sort-order module))
	 (*current-opinfo-table* (module-opinfo-table module))
	 (methods (method-lower-methods method *current-opinfo-table*)))
    (declare (type sort* coarity)
	     (type hash-table *current-sort-order* *current-opinfo-table*)
	     (type list methods))
    (let ((res nil))
      (dolist (meth methods)
	(declare (type method meth))
        (let ((new-coarity (method-coarity meth)))
	  (declare (type sort* new-coarity))
	  (when (and (not (member new-coarity res :test #'eq))
		     (sort<= (method-coarity meth) coarity))
	    (push (method-coarity meth) res)
	    )))
      res )))

;;; *MISC*
;;; METHOD-ALL-RULES

(defun method-all-rules (method &optional (opinfo-table *current-opinfo-table*))
  (declare (type method method)
	   (type hash-table opinfo-table)
	   (values list))
  (let ((dif (method-rules-with-different-top method opinfo-table))
	(ring (method-rules-with-same-top method opinfo-table))
	(res nil))
    (declare (type list dif)
	     (type rule-ring ring))
    (do ((rule (initialize-rule-ring ring) (rule-ring-next ring)))
	((end-of-rule-ring ring))
      (push rule res))
    (append dif res)))


;;; ********************
;;; OPERATOR CONSTRUCTOR
;;; ********************

;;; MAKE-OPERATOR-INTERNAL : name number-of-arguments module -> operator
;;;
;;; - handy function for making a new operator.
;;; - does not check that the operator already exists.
;;; - operator information is initialized as the following:
;;;  strategy : nil (unknown)
;;;  theory   : nil (unknown)
;;;  syntax   :
;;;     token-seq : computed
;;;     mixfix    : computed
;;;     type      : computed
;;;     prec      : nil (default value), may be set by operator attribute.
;;;     crec      : unknown, will be computed after all of the attributes are specified.
;;;     assoc     : nil (unknown), may be set by default attribute declarations.
;;;  print-name : computed

(defun make-operator-internal (name num-args module)
  (declare (type list name)
	   (type fixnum num-args)
	   (type module module)
	   (values operator))
  (let ((tseq (explode-operator-name name))
	(t-cnt 0))
    (dolist (s tseq)
      (when (eq s t)
	(incf t-cnt)))
    (when (and (> t-cnt 0)
	       (not (eql t-cnt num-args)))
      (with-output-chaos-error ()
	(format t "Mismatching number of arguments for op ~a, shold be ~d."
		name num-args)))
    (let ((op (allocate-operator name num-args module)))
      (declare (type operator op))
      ;; reset computable values
      (unless (the (or null opsyntax) (operator-syntax op))
	(setf (operator-syntax op) (make-opsyntax))
	(setf (operator-token-sequence op) tseq
	      (operator-is-mixfix op) (if (member t (operator-token-sequence op)
						  :test #'eq)
					  t
					nil))
	(setf (operator-syntactic-type op) (operator-syntactic-type-from-name
					    (operator-token-sequence op))))
      (setf (operator-print-name op)
	(cmake-operator-print-name op))
      ;; reset to default values.
      (setf (operator-strategy op) nil)
      (setf (operator-precedence op) nil)
      (setf (operator-associativity op) nil)
      (setf (operator-computed-precedence op) nil)
      (setf (operator-theory op) *the-empty-theory*)
      (set-context-module op module)
      op)))

;;; EOF
