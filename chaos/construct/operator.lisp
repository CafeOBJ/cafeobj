;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: operator.lisp,v 1.9 2010-07-29 07:45:27 sawada Exp $
(in-package :chaos)
#|=============================================================================
				  System:CHAOS
				Module:construct
			       File:operator.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; (defvar *on-operator-debug* nil)
(defun on-debug-operator ()
  (setq *on-operator-debug* t))
(defun off-debug-operator ()
  (setq *on-operator-debug* nil))

;;; *TODO, immediately*
;;;  syntax of an operator can be regular-expression.

;;; === DESCRIPTION ============================================================
;;; All of the procedures on operator, method.

;;;=============================================================================
;;;				    OPERATOR
;;;=============================================================================

;;; *****************************
;;; DECLARING OPERATOR ATTRIBUTES_____________________________________________
;;; *****************************

;;; Attributes declared by ":op-attr" construct are used as DEFAULT attributes
;;; value  of methods belonging to the operator.
;;; The following routines sets each attribute values from "attr" declarations.
;;; Each attributes are categorized in some groupes and stored in various slots 
;;; of operator object.

;;; Rewrite Strategy __________________________________________________________

;;; a sequnce of integers, declares rewrite strategy of reduction process.
;;; 

#-gcl(declaim (inline strategy-is-li?))
#-gcl
(defun strategy-is-li? (strat len)
  (declare (type list strat)
	   (type fixnum len)
	   (values (or null t)))
  (equal strat (the-default-strategy len)))

#+gcl
(si::define-inline-function strategy-is-li? (strat len)
  (equal strat (the-default-strategy len)))


;;; NOW we allow ANY use specified strategy. 1996/8/13. sawada.
;;; set ginven strategy as is.
;;; only error determined is out-of-bound.
;;;
(defun declare-operator-strategy (op strat)
  (declare (type operator op)
	   (type list strat)
	   (values list))
  (let ((num-args (operator-num-args op)))
    (declare (type fixnum num-args))
    (unless (and (listp strat)
		 (every #'(lambda (x) (and (integerp x) 
					   (<= (the fixnum x) num-args)))
			strat))
      (with-output-chaos-error ('invalid-op-attribute)
	(format t "invalid strategy ~a for opeator ~a, ignored."
		strat (operator-name op))
	))
    ;; 
    (setf (operator-strategy op) strat)))

(defun complete-strategy (num-args strat)
  (declare (ignore num-args)
	   (type fixnum num-args)
	   (type list strat)
	   (values list))
  ;; allow duplicated arg pos.
  ;; (setf strat (remove-duplicates strat))
  (let ((rest nil))
    #||
    (dotimes (x num-args)
      (unless (member (1+ x) strat :test #'(lambda (a b)
					     (eql (abs a) (abs b))))
	(push (1+ x) rest)))
    ||#
    (append strat
	    (if (member 0 strat) nil '(0))
	    (nreverse rest))))
      
;;; OPERATOR THEORY ____________________________________________________________

;;; <theory>     ::= ( <theory-elt>* )
;;;
(defvar .theory-code-table. )
(eval-when (:execute :load-toplevel :compile-toplevel)
  (setf .theory-code-table.
	'((:assoc . #..A.)
	  (:comm . #..C.)
	  (:idr . #..Z.)
	  (:id . #..Z.)
	  (:idem . #..I.)
	  )))
     
;;; *RESTRICTION*: NOW IDENTITY TERM MUST BE A CONSTANT.
;;; *TODO* : 
#||
(defun declare-operator-theory (operator theory &optional (module *current-module*))
  (declare (type operator operator)
	   (type list theory)
	   (type module module)
	   (values list))
  (let ((theory (compute-theory-from-attr-decl (operator-num-args operator)
					       theory
					       (operator-theory operator)
					       module)))
    (setf (operator-theory operator) theory) ))
||#

(defun compute-theory-from-attr-decl (arity theory-decl old-theory &optional (module *current-module*))
  (declare (type list arity)
	   (type list theory-decl)
	   (type (or null op-theory) old-theory)
	   (type module module))
  (unless old-theory (setf old-theory *the-empty-theory*))
  (let ((num-args (length arity))
	(code (theory-code old-theory))
	(t-code 0)
	(is-iden-r nil)
	(id nil))
    (declare (type fixnum num-args code)
	     (type (or null fixnum) t-code))
    (dolist (theory-elt theory-decl)
      (cond ((symbolp theory-elt)
	     (setf t-code (cdr (assq theory-elt .theory-code-table.)))
	     (unless t-code
	       (with-output-chaos-error ('invalid-op-attribute)
		 (princ "invalid opertor theory ")
		 (princ theory-elt)))
	     (setf code (logior code t-code)))
	    ((and (listp theory-elt) (= 2 (length theory-elt)))
	     (setq t-code
	       (cdr (assq (car theory-elt) .theory-code-table.)))
	     (unless t-code
	       (with-output-chaos-error ('invalid-op-attribute)
		 (princ "invalid operator theory ")
		 (princ theory-elt)))
	     (setq code (logior code t-code))
	     (setq id (if (consp (cadr theory-elt)) (cadr theory-elt)
			(cdr theory-elt)))
	     (when (eq (car theory-elt) ':idr) (setq is-iden-r t)))
	    (t (with-output-chaos-warning ()
		 (princ "unknown opertor theory ")
		 (princ theory-elt)
		 (princ ", ignored.")))))
    ;; identity
    (when id
      (prepare-for-parsing module)
      (let ((trm (simple-parse module id (car (maximal-sorts arity *current-sort-order*)))))
	(when (term-ill-defined trm)
	  (with-output-chaos-error ('invalid-op-attribute)
	    (format t "invalid identity term ~a" id)))
	(setq id trm)))

    ;; associativity
    (when (test-theory .A. code)
      (unless (= num-args 2)
	(with-output-chaos-warning ()
	  (princ "associativity theory is meaning-less for non-binary operators, ignored")
	  (setq code (unset-theory code .A.)))))

    ;; commutativity
    (when (test-theory .C. code)
      (unless (= num-args 2)
	(with-output-chaos-warning ()
	  (princ "commutativity theory is meaning-less for non-binary operators, ignored")
	  (setq code (unset-theory code .C.)))))

    ;; final result.
    (theory-make (theory-code-to-info code)
		 (if id (cons id is-iden-r)) )))

;;; ASSOCIATIVITY_______________________________________________________________

;;; syntactical associativity of infix operators, l-assoc or r-assoc. 
;;; similar to to (E e), or (e E) declaration of OBJ3.

(defun declare-operator-associativity (op assoc)
  (declare (type operator op)
	   (type (or simple-string symbol) assoc)
	   (values t))
  (if (stringp assoc)
      (setf assoc (intern assoc)))
  (case assoc
    ((:l-assoc |l-assoc| :left-associative |left-associative|)
     (setf (operator-associativity op) ':left))
    ((:r-assoc |r-assoc| :right-associative |right-associative|)
     (setf (operator-associativity op) ':right))
    (t (with-output-chaos-warning ()
	 (princ "unknown associativity declaration ")
	 (princ assoc)
	 (princ " for operator ")
	 (princ (operator-name op))
	 (princ ", ignored.")))))

;;; PRECEDENCE__________________________________________________________________
;;;

(defun declare-operator-precedence (op prec)
  (declare (type operator op)
	   (type (or simple-string fixnum) prec)
	   (values t))
  (if (stringp prec)
      (setf prec (read-from-string prec)))
  (unless (and (integerp prec)
	       (>= prec parser-min-precedence)
	       (<= prec parser-max-precedence))
    (with-output-chaos-warning ()
      (format t "operator precedence must be a natural number less than ~d, but ~d is given, ignored." parser-max-precedence prec)
      (return-from declare-operator-precedence nil)))
  (setf (opsyntax-prec (operator-syntax op)) prec))

;;; MEMO________________________________________________________________________
;;; memoize the rewriting result.
(defun compute-memo (attr)
  (if *memo-rewrite*			; (and *memo-rewrite* *always-memo*)
      t
    (let ((memo-decl (find-if #'(lambda (i)
				  (unless (atom i)
				    (equal "memo" (car i))))
			      attr)))
      (if memo-decl t nil))))

;; (defun declare-operator-memo-attr (op memo)
;;   (setf (operator-has-memo op) memo))

;;; ***************************
;;; DECLARING METHOD ATTRIBUTES_________________________________________________
;;; ***************************
;;; Explicit attributes of each method are declared by operator declaration
;;; forms by optional [ attrs ... ] construct.
;;; Attributes not declared explitly are taken from the operator to which the
;;; method belongs.
;;; The following routines manipulates explict declarations of the method
;;; attributes. 

;;; EQUATIONAL THEORY __________________________________________________________

(defun declare-method-theory (method attr &optional (info *current-opinfo-table*))
  (declare (type method method)
	   (type list attr)
	   (type hash-table info)
	   (values t))
  (let ((theory (compute-theory-from-attr-decl (method-arity method)
					       attr
					       (operator-theory (method-operator method info)))))
    (set-method-theory method theory info)))

(defun set-method-theory (method theory
				 &optional
				 (info *current-opinfo-table*)
				 (inherit nil))
  (declare (type method method)
	   (type op-theory theory)
	   (type hash-table info)
	   (type (or null t) inherit)
	   (values op-theory))
  (let ((new-th (check-method-theory-consistency method theory info inherit)))
    (setf (method-theory method info) new-th)
    (compute-method-theory-info-for-matching method info)
    new-th))

(defun check-method-theory-consistency (method theory info
					       &optional inherit
					                 no-merge)
  (declare (type method method)
	   (type op-theory theory)
	   (type hash-table info)
	   (type (or null t) inherit no-merge)
	   (values t))
  (let ((arity (method-arity method))
        (coarity (method-coarity method))
        (new-code (theory-code theory))
	(old-th (method-theory method info)))
    (declare (type list arity)
	     (type sort-struct coarity)
	     (type fixnum new-code)
	     (type (or null op-theory) old-th))
    ;;
    (unless no-merge
      (when (and old-th (not (eq theory old-th)))
	(setq theory (merge-operator-theory-in *current-module*
					       method
					       old-th
					       theory
					       ))
	(setq new-code (theory-code theory))))
    ;;
    ;; associativity
    ;;
    (when (theory-contains-associativity theory)
      (unless (and (is-in-same-connected-component coarity (car arity) *current-sort-order*)
		   (is-in-same-connected-component coarity (cadr arity) *current-sort-order*)
		   (is-in-same-connected-component (car arity) (cadr arity) *current-sort-order*))
	;; should always check
	(unless inherit
	  (with-output-chaos-warning ()
	    (format t "rank of method ")
	    (print-chaos-object method)
	    (print-next)
	    (format t "does not allow it to be associative, ignoring `assoc' attribute.")))
	(setf new-code (unset-theory new-code .A.))))
    ;;
    ;; commutativity
    ;;
    (when (theory-contains-commutativity theory)
      (unless (is-in-same-connected-component (car arity) (cadr arity) *current-sort-order*)
	;;
	(unless inherit
	  (with-output-chaos-warning ()
	    (princ "commutative operations, their arguments must be of the same connected component.")
	    (print-next)
	    (princ "`comm' attribute of operation ")
	    (print-chaos-object method)
	    (princ " is ignored.")))
	(setf new-code (unset-theory new-code .C.))))
    ;;
    ;; identity
    ;;
    (when (theory-contains-identity theory)
      (let* ((id (car (theory-zero theory)))
	     (id-sort (term-sort id)))
	(if (not (and (= 2 (length arity))
		      (is-in-same-connected-component (car arity) (cadr arity) *current-sort-order*)
		      (is-in-same-connected-component (car arity) coarity *current-sort-order*)))
	    (unless inherit
	      (with-output-chaos-warning ()
		(princ "id: makes sense only when the operator is binary,")
		(print-next)
		(princ "and its arity sorts and the coarity sort are of same connected components.")
		(print-next)
		(princ "ignoring id:(idr:) attribute of operator ")
		(print-chaos-object method)
		(setf new-code (unset-theory new-code .Z.)))
	    (unless (and (sort<= id-sort (car (method-arity method))
				 *current-sort-order*)
			 (sort<= id-sort (cadr (method-arity method))
				 *current-sort-order*))
	      (unless inherit
		(with-output-chaos-warning ()
		  (princ "id: makes sense the identity term belongs to the arity sort.")
		  (print-next)
		  (princ "ignoreing id:(idr:) attribute of operator ")
		  (print-chaos-object method))
		(setf new-code (unset-theory new-code .Z.)))) ))))
    ;;
    (unless (= new-code (theory-code theory))
      (setf theory (theory-make (theory-code-to-info new-code)
                                (if (theory-contains-identity theory)
				    (theory-zero theory)
				    nil))))
    ;; (format t "~%** #4 - ~a" new-code)
    (when (and inherit
	       (theory-contains-associativity theory)
	       (null (method-associativity method)))
      (setf (method-associativity method) :right))
    (setf (method-theory method info) theory)
    (compute-method-theory-info-for-matching method info)
    ;; returns the final result
    theory ))
         
(defun merge-operator-theory-in (mod method th1 th2)    
  (declare (ignore mod)
	   (type module mod)
	   (type method method)
	   (type (or null op-theory) th1 th2)
	   (values op-theory))
  (if (null th1)
      th2
      (let ((code1 (theory-code th1))
	    (zero1 (theory-zero th1))
	    (code2 (theory-code th2))
	    (zero2 (theory-zero th2))
	    (new-theory nil))
	;;
	(if (= code1 code2)
	    th2
	    (let ((new-code (logior code1 code2))
		  (zero nil))
	      (setq new-theory (create-theory new-code nil))
	      (setq zero
		    (if (null zero1)
			zero2
			(if (null zero2)
			    zero1
			    (if (equal zero1 zero2)
				zero1
				(with-output-chaos-warning ()
				  (format t "variation in identity of method ")
				  (print-chaos-object method)
				  (print-next)
				  (format t "re setting it to ")
				  (print-chaos-object zero)
				  nil)
				))))
	      (setf (theory-zero new-theory) zero)
	      new-theory)))))

;;; REWRITE STRATEGY____________________________________________________________

(defun declare-method-strategy (meth strat &optional (info *current-opinfo-table*))
  (declare (type method meth)
	   (type list strat)
	   (type hash-table info)
	   (values list))
  (let ((num-args (operator-num-args (method-operator meth info))))
    (declare (type fixnum num-args))
    (unless (and (listp strat)
		 (every #'(lambda (x) (and (integerp x) 
					   (<= (the fixnum x) num-args)))
			strat))
      (with-output-chaos-error ('invalid-op-attribute)
	(princ "invalid strategy ")
	(princ strat)
	(princ " for operator ")
	(princ (method-symbol meth))
	))
    ;; complete
    (setf (method-supplied-strategy meth) (complete-strategy num-args strat))))
  
;;; ASSOCIATIVITY _______________________________________________________________

(defun declare-method-associativity (meth assoc)
  (declare (type method meth)
	   (type (or simple-string symbol) assoc)
	   (values t))
  (if (stringp assoc)
      (setf assoc (intern assoc)))
  (case assoc
    ((:l-assoc |l-assoc| :left-associative |left-associative|)
     (setf (method-associativity meth) ':left))
    ((:r-assoc |r-assoc| :right-associative |right-associative|)
     (setf (method-associativity meth) ':right))
    (t (with-output-chaos-warning ()
	 (format t "unknown associativity declaration ~a assoc for operator ~a, ignored"
		 assoc
		 (method-symbol meth)
		 ))
       nil)))

;;; PRECEDENCE ___________________________________________________________________

(defun declare-method-precedence (meth prec)
  (declare (type method meth)
	   (type (or simple-string fixnum) prec)
	   (values (or null fixnum)))
  (if (stringp prec)
      (setf prec (read-from-string prec)))
  (unless (and (integerp prec)
	       (>= prec parser-min-precedence)
	       (<= prec parser-max-precedence))
    (with-output-chaos-warning ()
      (format t "operator precedence must be a natural number between ~d and ~d, but ~d is given, ignored."
	      parser-min-precedence parser-max-precedence
	      prec)
      (return-from declare-method-precedence nil)))
  (setf (method-precedence meth) prec))

;;; MEMO __________________________________________________________________________

(defun declare-method-memo-attr (method memo)
  (setf (method-has-memo method) memo))

;;; DECIDABLE PREDICATE ___________________________________________________________
(defun declare-method-meta-demod-attr (method meta-demod)
  (setf (method-is-meta-demod method) meta-demod))

;;; CONSTRUCTOR ___________________________________________________________________

(defun declare-method-constr (method constr)
  (declare (type method method)
	   (type (or null t) constr)
	   (values (or null t)))
  (setf (method-constructor method) constr)
  (when constr
    (pushnew method (sort-constructor (method-coarity method))
	     :test #'eq))
  )

;;; COHERENCY ---------------------------------------------------------------------

(defun declare-method-coherent (method coherent)
  (declare (type method method)
	   (type (or null t) coherent)
	   (values (or null t)))
  (setf (method-coherent method) coherent))

;;; COPIER ________________________________________________________________________
;;; COPY-METHOD-INFO : from-method to-method
;;;
#|| NOT USED
(defun copy-method-info (from to)
  (let (sup-strat
	theory
	prec
	memo
	assoc
	constr)
    (when *on-operator-debug*
      (format t "~&[copy-method-info]:")
      (format t "~&-- copy from ") (print-chaos-object from)
      (format t "~&        to   ") (print-chaos-object to))
    (let ((from-module (method-module from)))
      (with-in-module (from-module)
	(setf sup-strat (method-supplied-strategy from)
	      theory (method-theory from)
	      prec (get-method-precedence from)
	      memo (method-memo from)
	      assoc (method-associativity from)
	      constr (method-constructor from))))
    (let ((to-module (method-module to)))
      (with-in-module (to-module)
	(setf (method-supplied-strategy to) sup-strat
	      (method-theory to) theory
	      (method-precedence to) prec
	      (method-memo to) memo
	      (method-associativity to) assoc
	      (method-constructor to) constr)))
    ))

||#

;;; ********************
;;; OPERATOR DECLARATION _______________________________________________________
;;; ********************

;;; NOTE: *assumption: all sorts are registed in the module

(defun declare-operator-in-module (op-name arity coarity module
					   &optional
					   constructor
					   behavioural
					   coherent
					   error-operator)
					   
  (declare (type t op-name)
	   (type list arity)
	   ;; (type (or symbol sort* list string) coarity)
	   (type (or null t) constructor behavioural coherent
		 error-operator)
	   (values (or null operator) (or null method) (or null t)))
  ;;
  (let* ((mod (if (module-p module)
		  module
		  (find-module-in-env module))))
    (unless mod
      (with-output-chaos-error ('no-such-module)
	(princ "declaring operator, no such module ")
	(princ module)
	))

    ;; check arity, coarity
    (with-in-module (mod)
      (let ((r-arity nil)
	    (r-coarity coarity))
	(dolist (a arity)
	  (let ((s (if (sort-struct-p a) a (find-sort-in mod a))))
	    (when (and (err-sort-p s)
		       (not error-operator))
	      (return-from declare-operator-in-module
		(values nil nil t)))
	    (unless s
	      (cond ((and (not error-operator)
			  (may-be-error-sort-ref? a))
		     ;; may declaration of error operator
		     ;; the process is postponed
		     (return-from declare-operator-in-module
		       (values nil nil t)))
		    (t (with-output-chaos-error ('no-such-sort)
			 (princ "declaring operator, no such sort ")
			 (print-sort-ref a)
			 ))))
	    (push s r-arity)))
	(setf r-coarity (if (sort-struct-p coarity)
			    coarity
			    (find-sort-in mod coarity)))
	(when (and (err-sort-p r-coarity)
		   (not error-operator))
	  (return-from declare-operator-in-module
	    (values nil nil t)))
	;;
	(unless r-coarity
	  (cond ((and (not error-operator)
		      (may-be-error-sort-ref? coarity))
		 (return-from declare-operator-in-module
		   (values nil nil t)))
		(t 
		 (with-output-chaos-error ('no-such-sort)
		   (princ "declaring operator, no such sort ")
		   (print-sort-ref coarity)
		   ))))
	;; name conflict check with existing variables
	#||
	(when (and (null r-arity)
		   (find-variable-in module (car op-name)))
	  (with-output-chaos-warning ()
	    (format t "declaring op ~s" op-name)
	    (print-next)
	    (princ "     there already a variable with the same name.")
	    (princ " ... ignoring"))
	  (return-from declare-operator-in-module (values nil nil nil))
	  )
	||#
	;;
	(multiple-value-bind (x y)
	    (add-operator-declaration-to-module op-name
						(nreverse r-arity)
						r-coarity
						mod
						constructor
						behavioural
						coherent
						error-operator
						)
	  (values x y nil))))
    ))

(defun make-operator-in-module (op-name num-args module &optional qual-name)
  (declare (ignore qual-name)
	   (type t op-name)
	   (type fixnum num-args)
	   (type module module)
	   (type t qual-name)
	   (values operator))
  (let ((op (make-operator-internal op-name num-args module)))
    op))

(defun check-overloading-with-builtin (op-name arity coarity module)
  (unless arity
    (let ((opstr (car op-name))
	  (sorts (module-all-sorts module)))
      (dolist (bi sorts)
	(when (sort-is-builtin bi)
	  (let ((token-pred (bsort-token-predicate bi)))
	    (when (and token-pred
		       (funcall token-pred opstr)
		       (is-in-same-connected-component* coarity
							bi
							(module-sort-order module)))

	      (with-output-chaos-warning ()
		(format t "operator name ~s is overloaded with built-in constant of sort " opstr)
		(print-sort-name bi module)
		(print-next)
		(princ "... ignored.")
		(return-from check-overloading-with-builtin t)
		))))))
    )
  nil)

(defun add-operator-declaration-to-module (op-name arity coarity module
						   &optional
						   constructor
						   behavioural
						   coherent
						   error-operator)
  (declare (type t op-name)
	   (type list arity)
	   (type (or symbol sort-struct) coarity)
	   (type t module)
	   (type (or null t)
		 constructor behavioural coherent error-operator))
  (let* ((mod (if (module-p module)
		  module
		  (find-module-in-env module)))
	 (op-infos (find-operators-in-module op-name (length arity) mod))
	 (opinfo nil)
	 (op nil))
    (declare (type module mod)
	     (type list op-infos))
    ;;
    (when *on-operator-debug*
      (format t "~%[add-operator-declaratoin-to-module]: called with")
      (format t "~% -- op-name = ~a, arity = ~a, coarity = ~a" op-name
	      arity coarity)
      (format t "~% -- module = ~a, constructor = ~a, behavioural = ~a"
	      module constructor behavioural)
      (format t "~% -- coherent = ~a, error-operator = ~a" coherent error-operator)
      )
    ;; checks hidden sort condition
    (let ((hidden? nil))
      (dolist (as arity)
	(when (sort-is-hidden as)
	  (if (and hidden? behavioural)
	      (with-output-chaos-error ('invalid-op-decl)
		(format t "more than one hidden sort in the declaration of operator \"~{~a~}\""
		       op-name)
		))
	  (setf hidden? t)
	  #|| -----------------------------------------------
	  (when (and (not (sort= as *huniversal-sort*))
		     (not (eq module (sort-module as)))
		     behavioural)
	    (with-output-chaos-warning ()
	      (format t "behavioural operator \"~{~a~}\" has imported hidden sort " op-name)
	      (print-sort-name as)
	      (princ " in its arity.")
	      ))
	  --------------------------------------------------- ||#
	  ))
      #|| NULL argument is acceptable...2012/6/28
      (when (and behavioural (not hidden?))
	(with-output-chaos-error ('invalid-op-decl)
	  (format t "behavioural operator must have exactly one hidden sort in its arity")
	  ))
      ||#
      (when (and behavioural coherent)
	(with-output-chaos-error ('invalid-op-decl)
	  (format t "coherency is meaningless for behavioural operator.")
	  ))
      (when (and coherent (not (some #'(lambda (x) (sort-is-hidden x)) arity)))
	(with-output-chaos-error ('invalid-op-decl)
	  (format t "coherency is only meaningfull for operator with hidden sort in its arity.")
	  ))
      )

    ;;
    (when *builtin-overloading-check*
      (when (check-overloading-with-builtin op-name arity coarity module)
	(return-from add-operator-declaration-to-module nil)))
    ;;
    
    ;; uses pre-existing operator if it is the apropreate one,
    ;; i.e.,
    ;;  (1) has method with coarity which is in the same connected component.
    ;;  or
    ;;  (2) operator of own module. -- this isn't good, so now deleted
    ;;  (3) constants are always put into the same group.
    ;;  (4) if_then_else_fi is VERY specially treated.
    ;;
    (when op-infos
      (dolist (x op-infos)
	(let ((xcoarity (method-coarity (car (opinfo-methods x)))))
	  (when (or (null arity)	; constants always ...
		    (equal op-name '("if" "_" "then" "_" "else" "_" "fi"))
		    (is-in-same-connected-component* coarity
						     xcoarity
						     (module-sort-order mod)))

	    (when *chaos-verbose* ;; *on-operator-debug*
	      (with-output-simple-msg ()
		(format t "~&declaring overloading operator ~a : "
			(operator-name (opinfo-operator x)))
		(when arity
		  (print-sort-list arity mod))
		(princ " -> ")
		(print-sort-name coarity mod)
		(print-next)))
	    ;;
	    (setf op (opinfo-operator x))
	    (setf opinfo x)
	    (return)))))

    ;; create a new operator iff there is not the same one.
    (unless op
      (setq op (make-operator-internal op-name (length arity) mod))
      (setq opinfo (make-opinfo :operator op))
      (push opinfo (module-operators mod))
      (push opinfo (module-all-operators mod))
      (symbol-table-add (module-symbol-table mod) op-name op)
      (when *on-operator-debug*
	(format t "~&opdecl: created new operator ~a" (operator-name op)))
		
      )
    ;;
    (multiple-value-bind (ent? meth)
	(add-operator-declaration-to-table opinfo
					   arity
					   coarity
					   mod
					   constructor
					   behavioural
					   coherent
					   error-operator)
      (declare (type (or null t) ent?)
	       (type method meth))
      (when ent? (setf (method-module meth) module))
      (mark-need-parsing-preparation mod)
      (values op meth))))

;;; OPERATOR ATTRIBUTES ________________________________________________________

(defmacro find-operator-or-warn (?_?opname ?!?number-of-args ?$?module)
  (once-only (?_?opname ?!?number-of-args ?$?module)
  `(or (find-qual-operator-in ,?$?module ,?_?opname ,?!?number-of-args)
       (progn (with-output-chaos-warning ()
		(princ "no such operator ")
		(print-chaos-object ,?_?opname)
		(princ "in module ")
		(print-mod-name ,?$?module))
	      nil))))

(defun declare-operator-strategy-in-module (op-name number-of-args
						    strategy
						    &optional
						    (module *current-module*) )
  (declare (type t op-name)
	   (type fixnum number-of-args)
	   (type list strategy)
	   (type module module)
	   (values t))
  (let ((opinfo (find-operator-or-warn op-name number-of-args module)))
    (unless opinfo (return-from declare-operator-strategy-in-module nil))
    (declare-operator-strategy (opinfo-operator opinfo) strategy)))

(defun declare-operator-precedence-in-module (op-name number-of-args
						      prec
						      &optional
						      (module
						       *current-module*))
  (declare (type t op-name)
	   (type fixnum number-of-args prec)
	   (type module module)
	   (values t))
  (let ((opinfo (find-operator-or-warn op-name number-of-args module)))
    (unless opinfo (return-from declare-operator-precedence-in-module nil))
    (declare-operator-precedence (opinfo-operator opinfo) prec)))

#||
(defun declare-operator-theory-in-module (op-name number-of-args
						  theory
						  &optional
						  (module
						   *current-module*))
  (declare (type t op-name)
	   (type fixnum number-of-args)
	   (type op-theory theory)
	   (type module module)
	   (values t))
  (let ((opinfo (find-operator-or-warn op-name number-of-args module)))
    (unless opinfo (return-from declare-operator-theory-in-module nil))
    (declare-operator-theory (opinfo-operator opinfo)  theory)))
||#

(defun declare-operator-associativity-in-module (op-name number-of-args
							 assoc
							 &optional
							 (module
							  *current-module*))
  (declare (type t op-name)
	   (type fixnum number-of-args)
	   (type symbol assoc)
	   (type module module)
	   (values t))
  (let ((opinfo (find-operator-or-warn op-name number-of-args module)))
    (unless opinfo
      (with-output-chaos-error ('invalid-op-name)
	(format t "declaring associativity: no such operator ~a" op-name)
	))
    (declare-operator-associativity (opinfo-operator opinfo)  assoc)))
				   

;;; ************
;;; METHOD-TABLE
;;; ************

;;;   A method-table is used for assigning terms the lest sort and find appropriate
;;;   method of an operator.
;;;   This is created per an operator and stored in opinfo which is associated to each
;;;   operator in a module.
;;;
;;;  MAKE-METHOD-TABLE
;;;
;;;       Int  Nat -> Nat      method-1
;;;       Nat  Int -> Nat      method-2
;;;       Int  Int -> Int      method-3
;;;       Nat  Nat -> Nat      method-4
;;;       Bool Bool -> Bool    method-5
;;;              |
;;;              V
;;;  low
;;;   |   Nat   Nat -> Nat     method-4
;;;   |   Nat   Int -> Nat     method-2
;;;   |   Int   Nat -> Nat     method-1
;;;   V   Int   Int -> Int     method-3
;;;  high
;;;              +
;;;       Bool Bool -> Bool    method-5
;;;
;;;   \\ implementation
;;;
;;;     ( ( (Nat ( (Nat . (method-4))
;;;                (Int . (method-2)) )
;;;         )
;;;         (Int arg-2 ( (Nat . (method-1))
;;;                      (Int . (method-3)) )
;;;         )
;;;        )
;;;       ( (Bool ( (Bool . (method-5)) )
;;;          )
;;;       )
;;;      )
;;;
;;; NOTE: ASSUMPTION
;;;      Signature is regularized, error sorts are generated and operator declarations
;;;      for each error sorts are generated.
;;;--------------------------------------------------------------------------------
;;;

(defun make-method-table (list-of-method
			  &optional
			  (so *current-sort-order*))
  (declare (type list list-of-method)
	   (type hash-table so)
	   (values t))
  (let ((op (method-operator (car list-of-method))))
    (make-method-table-internal list-of-method
				0
				(operator-num-args op)
				so)))

(defun make-method-table-internal (list-of-method arg-pos num-args so)
  (declare (type list list-of-method)
	   (type fixnum arg-pos num-args)
	   (type hash-table so))
  ;;
  ;;(debug-msg ("~%===================================================="))
  ;;(debug-msg ("~%arg-pos = ~d") arg-pos)
  ;;(debug-msg ("~%mathods = ~s") list-of-method)
  ;;;
  (if (= 0 num-args)
      ;; we assume the signature is regular, thus, constants has only one
      ;; declaration and it has no declaration for erro sort. 
      list-of-method
      (if (< arg-pos num-args)
	  (flet ((get-minimal-methods ()
		   (let ((sorts (mapcar #'(lambda (arity) (nth arg-pos arity))
					(mapcar #'(lambda (x) (method-arity x))
						list-of-method)))
			 (res nil))
		     (declare (type list sorts res))
		     (dolist (m list-of-method res)
		       ;; (declare (type operator-method m))
		       (let ((m-sort (nth arg-pos (method-arity m))))
			 (when (or (not (intersection (subsorts m-sort so)
						      sorts :test #'eq))
				   (and (= arg-pos 0) (or (method-is-error-method m)
							  (method-is-universal m))))
			   (let ((pos (assoc m-sort res :test #'eq)))
			     (declare (type list pos))
			     (if pos
				 (push m (cdr pos))
				 (push (list m-sort m) res))))))))
		 (find-comparable (sort)
		   (let ((res nil))
		     (declare (type list res))
		     (dolist (m list-of-method res)
		       ;; (declare (type operator-method m))
		       (if (and (or (not (err-sort-p (method-coarity m)))
				    (not (or (sort= (method-coarity m) *universal-sort*)
					     (sort= (method-coarity m) *huniversal-sort*))))
				(sort< sort (nth arg-pos (method-arity m)) so))
			   (push m res))))))
	    (let ((minimal-methods (get-minimal-methods)))
	      (declare (type list minimal-methods))
	      ;;(debug-msg ("~%minimal-methods: ~s") minimal-methods)
	      (let* ((num-entry (length minimal-methods))
		     (result (make-list num-entry)))
		(declare (type fixnum num-entry)
			 (type list result))
		(dotimes (x num-entry)
		  (declare (type fixnum x))
		  (let* ((s-ms (nth x minimal-methods))
			 (comparable-methods (find-comparable (car s-ms))))
		    (declare (type list s-ms comparable-methods))
		    ;;(debug-msg ("~%comparable-methods: ~s") comparable-methods)
		    (setf (nth x result)
			  (cons (cons (car s-ms)
				      (if (= arg-pos (1- num-args))
					  (cdr s-ms)
					  (make-method-table-internal
					   (append (cdr s-ms) comparable-methods)
					   (1+ arg-pos)
					   num-args
					   so)))
				(if comparable-methods
				    (make-method-table-internal comparable-methods
								arg-pos
								num-args
								so)
				    nil)))))
		result)))
	  )))
    
			       
;;; FIND-OPERATOR-METHOD operator arg-sort-list & optional opinfo-table sort-order
;;; 
(defmacro find-operator-method (?__?op ?__?arg-sort-list
				       &optional
				       ;; (opinfo-table '*current-opinfo-table*)
				       (??_??sort-order '*current-sort-order*))
  `(find-method-in-table ,?__?arg-sort-list
                         (operator-method-table ,?__?op)
                         ,??_??sort-order))

;;; FIND-METHOD-IN-TABLE sort-list method-table sort-order
;;;
(defun find-method-in-table (sort-list method-table sort-order  &aux (method nil))
  (declare (type list sort-list)
	   (type list method-table)
	   (type hash-table sort-order))
  (if sort-list
      (block find
	(dolist (method-entry method-table)
	  ;; check for each incomparable ranks.
	  (cond ((sort<= (car sort-list) (caar method-entry) sort-order)
		 (if (operator-method-p (car (cdar method-entry)))
		     (return-from find (cdar method-entry))
		     (setf method (find-method-in-table (cdr sort-list)
							(cdar method-entry)
							sort-order)))
		 (when method (return-from find method)))
		(t (setf method
			 (find-method-in-table sort-list (cdr method-entry) sort-order))
		   (when method (return-from find method))
		   ))))
      ;; constant. only one method.
      method-table
      ))
				
;;; *****************
;;; ADDING NEW METHOD___________________________________________________________
;;; *****************

;;; ADD-OPERATOR-DECLARATION-TO-TABLE : OPINFO ARITY COARITY -> METHOD
;;;-----------------------------------------------------------------------------
;;; NOTE: Some module independent information of an operator(operator attributes
;;;       such as theory and rewrite strategy) are not copied by this function.
;;;       They are declared separately with operator declarations.
;;;
(defun add-operator-declaration-to-table (opinfo
					  arity
					  coarity
					  &optional
					  (module
					   (or *current-module* *last-module*))
					  constructor
					  behavioural
					  coherent
					  error-operator)
  (declare (type list opinfo arity)
	   (type sort-struct coarity)
	   (type module module)
	   (type (or null t)
		 constructor
		 behavioural
		 coherent
		 error-operator)
	   (values (or null t) method))
  ;;
  (let ((meth nil))
    (dolist (m (opinfo-methods opinfo))
      (when (and (sort-list= (method-arity m) arity)
		 (sort= (method-coarity m) coarity))
	(setq meth m)
	(return nil)))
    (when (and meth
	       (not (eq (method-name meth )
			(method-name *beh-equal*)))
	       (not (method-is-error-method meth)))
	       ;; (and meth *on-operator-debug*)
      (with-output-chaos-warning ()
	(format t "the operator of the same rank has already been declared: ")
	(print-next)
	(print-chaos-object meth)
	(print-next)
	(format t "~%... ignored.")
	;; (print-next)
	;; (format t "ignoring this one.")
	)
      #||
      (return-from add-operator-declaration-to-table
	(values nil meth))
      ||#
      )
    (let ((operator (opinfo-operator opinfo)))
      (declare (type operator operator))
      (when (and meth (not (eq (method-module meth) module)))
	(when (and (not (method-constructor meth))
		   constructor)
	  (with-output-chaos-warning ()
	    (princ "operator ")
	    (print-chaos-object meth)
	    (print-next)
	    (princ "was NOT constructor in module ")
	    (print-simple-mod-name (method-module meth))
	    (print-next)
	    (princ "but being declared as constructor in ")
	    (print-simple-mod-name module)
	    (print-next)
	    (princ "ignoring `constr' attribute.")))
	(unless (eq (method-is-behavioural meth) behavioural)
	  (with-output-chaos-warning ()
	    (princ "operator ")
	    (print-chaos-object meth)
	    (print-next)
	    (princ "cannot be behvioural and not at the same time")
	    (print-next)
	    (princ "ignoring ...")))
	(when (and (not (method-is-coherent meth)) coherent)
	  (with-output-chaos-warning ()
	    (princ "operator ")
	    (print-chaos-object meth)
	    (print-next)
	    (princ "was not coherent in module ")
	    (print-simple-mod-name (method-module meth))
	    (print-next)
	    (princ "but being declared as coherent in ")
	    (print-simple-mod-name module)
	    #||
	    (print-next)
	    (princ "ignoring this `coherent' attribute.")
	    ||#
	    )))
      (unless meth
	(setq meth (make-operator-method :name (operator-name operator)
					 :arity arity
					 :coarity coarity
					 )))
      (when (eq (method-module meth) module)
	(setf (method-constructor meth) constructor)
	(setf (method-is-behavioural meth) behavioural)
	;; (setf (method-is-coherent meth) coherent)
	(setf (method-is-user-defined-error-method meth)
	      error-operator))
      ;;
      (let ((res1 (add-method-to-table opinfo meth module)))
	(setf (method-is-coherent meth) coherent)
	(when constructor
	  (pushnew meth (sort-constructors (method-coarity meth))
		   :test #'eq))
	;;
	(values res1 meth)))))

;;; ADD-METHOD-TO-TABLE : OPINFO METHOD -> Bool
;;;-----------------------------------------------------------------------------

(defun add-method-to-table (opinfo method module)
  (declare (type list opinfo)
	   (type method method)
	   (type module module)
	   (values (or null t)))
  (let ((method-info-table (module-opinfo-table module)))
    (declare (type hash-table method-info-table))
    (if (not (find method (opinfo-methods opinfo)
		   :test #'(lambda (x y)
			     (declare (type method x y))
			     (and (sort-list= (method-arity x)
					      (method-arity y))
				  (sort= (method-coarity x)
					 (method-coarity y))))))
	(progn
	  (when *on-operator-debug*
	    (format t "~& - add ")
	    (print-method method)
	    (format t " ==> ~a."
		    (operator-symbol (opinfo-operator opinfo)))
	    (print-mod-name (operator-module (opinfo-operator opinfo))))
	  (setf (get-method-info method method-info-table)
		(make-method-info method
				  module	; was *current-module*
				  (opinfo-operator opinfo)))
	  (push method (opinfo-methods opinfo))
	  (setf (opinfo-method-table opinfo) nil)
	  (when (and (some #'(lambda (x) (sort-is-hidden x))
			   (method-arity method))
		     (or (method-is-user-defined-error-method method)
			 (not (method-is-error-method method))))
	    (if (method-is-behavioural method)
		(if (sort-is-hidden (method-coarity method))
		    (push method (module-beh-methods module))
		  (push method (module-beh-attributes module)))
	      (if (sort-is-hidden (method-coarity method))
		  (push method (module-non-beh-methods module))
		(push method (module-non-beh-attributes module)))))
	  t)
      nil)))

(defun add-method-to-table-fast (opinfo method module)
  (declare (type list opinfo)
	   (type method method)
	   (type module module)
	   (values t))
  (let ((method-info-table (module-opinfo-table module)))
    (when *on-operator-debug*
      (format t "~& - add ")
      (print-method method)
      (format t " ==> ~a."
	      (operator-symbol (opinfo-operator opinfo)))
      (print-mod-name (operator-module (opinfo-operator opinfo))))
    (unless (get-method-info method method-info-table)
      (setf (get-method-info method method-info-table)
	    (make-method-info method
			      module
			      (opinfo-operator opinfo))))
    (setf (opinfo-method-table opinfo) nil)
    (when (and (some #'(lambda (x) (sort-is-hidden x)) (method-arity method))
	       (or (method-is-user-defined-error-method method)
		   (not (method-is-error-method method))))
      (if (method-is-behavioural method)
	  (if (sort-is-hidden (method-coarity method))
	      (pushnew method (module-beh-methods module) :test #'eq)
	    (pushnew method (module-beh-attributes module) :test #'eq))
	(if (sort-is-hidden (method-coarity method))
	    (pushnew method (module-non-beh-methods module) :test #'eq)
	  (pushnew method (module-non-beh-attributes module) :test #'eq))
	))
    (pushnew method (opinfo-methods opinfo) :test #'eq)
    ))

(defun add-method-to-table-very-fast (opinfo method module)
  (declare (type list opinfo)
	   (type method method)
	   (type module module)
	   (values t))
  (when (and (some #'(lambda (x) (sort-is-hidden x)) (method-arity method))
	     (or (method-is-user-defined-error-method method)
		 (not (method-is-error-method method))))
    (if (method-is-behavioural method)
	(if (sort-is-hidden (method-coarity method))
	    (push method (module-beh-methods module))
	  (push method (module-beh-attributes module)))
      (if (sort-is-hidden (method-coarity method))
	  (push method (module-non-beh-methods module))
	(push method (module-non-beh-attributes module)))))
  (push method (opinfo-methods opinfo))
  )

;;;
;;; RECREATE-METHOD
;;;
;;; NOTE* this function does not maintain Identity in THEORY of
;;;       new method.
;;; ************************************************************
(defun recreate-method (old-module meth
				   new-module
				   op-symbol
				   arity
				   coarity &optional sort-map)
  (let (sup-strat
	theory
	prec
	assoc
	constr
	behavioural
	coherent
	memo
	id-symbol
	meta-demod
	error-operator)
    (with-in-module (old-module)
      (setq sup-strat (method-supplied-strategy meth)
	    theory (method-theory meth)
	    prec (get-method-precedence meth)
	    assoc (method-associativity meth)
	    constr (method-constructor meth)
	    behavioural (method-behavioural meth)
	    coherent (method-coherent meth)
	    memo (method-has-memo meth)
	    meta-demod (method-is-meta-demod meth)
	    id-symbol (method-id-symbol meth)
	    error-operator (method-is-user-defined-error-method
			    meth)))
    (with-in-module (new-module)
      (when error-operator
	(let* ((o-arity (method-arity meth))
	       (len (length o-arity))
	       (new-arity (copy-list arity)))
	  (dotimes (x len)
	    (when (err-sort-p (nth x o-arity))
	      (setf (nth x new-arity)
		    (find-compatible-err-sort (nth x o-arity)
					      new-module
					      sort-map))))
	  (setq arity new-arity)
	  (when (err-sort-p (method-coarity meth))
	    (setq coarity (find-compatible-err-sort (method-coarity meth)
						    new-module
						    sort-map)))))
      ;;
      (multiple-value-bind (newop newmeth)
	  (declare-operator-in-module op-symbol
				      arity
				      coarity
				      new-module
				      constr
				      behavioural
				      coherent
				      error-operator)
	(declare (ignore newop))
	(setf (method-supplied-strategy newmeth) sup-strat
	      (method-precedence newmeth) prec
	      (method-associativity newmeth) assoc)
	(setf (method-derived-from newmeth) meth)
	(setf (method-has-memo newmeth) memo)
	(setf (method-is-meta-demod newmeth) meta-demod)
	(setf (method-id-symbol newmeth) id-symbol)
	;;
	;; check identity in theory
	(if (theory-contains-identity theory)
	    (let ((zero (theory-zero theory)))
	      (setq zero (cons '%to-rename zero))
	      (setf (method-theory newmeth)
		    (theory-make (theory-info theory) zero))
	      (compute-method-theory-info-for-matching newmeth)
	      )
	    ;;
	    (progn
	      (setf (method-theory newmeth) theory)
	      (compute-method-theory-info-for-matching newmeth)
	      ))
	;;
	newmeth))))
	
;;; ******************************
;;; PREPARATIONS FOR PARSING TERMS______________________________________________
;;; ******************************

;;; SETUP-OPERATOR-METHODS operator-info
;;;-----------------------------------------------------------------------------
;;; 1. Generate default methods & make method lookup table.
;;; 2. Set attributes default values if they are not explicitly declared.
;;; NOTE: assumption -- module is regularized
;;;                  -- sort-order is up-to-date
;;;                  -- error sorts are generated
;;;                  -- operator attributes are set.
;;; NOTE: computing default rewrite strategy for each method must be done
;;;       AFTER all axioms. thus separated to another routine
;;;       (see `compute-rew-strategy').
;;; !! ASSUME BEING EXECUTED IN THE CONTEXT OF `WITH-IN-MODULE'.
;;; 
(defun method< (meth1 meth2 &optional (so *current-sort-order*))
  (declare (type method meth1 meth2)
	   (type hash-table so)
	   (values (or null t)))
  (let ((coar1 (method-coarity meth1))
	(coar2 (method-coarity meth2)))
    (or (sort< coar2 coar1 so)
	(and (sort= coar1 coar2)
	     (sort-list<= (method-arity meth2) (method-arity meth1) so)))
    ))

;;;
;;; DELETE-ERROR-OPERATORS-IN
;;;
(defun delete-error-operators-in (&optional (module (or *current-module*
							*last-module*)))
  (declare (type module module)
	   (values t))
  (let ((minfo (module-opinfo-table module))
	(err-ops nil))
    (maphash #'(lambda (meth info)
		 (declare (ignore info))
		 (when (and (method-is-error-method meth)
			    (not (method-is-user-defined-error-method meth)))
		   (push meth err-ops)))
	     minfo)
    (dolist (m err-ops)
      (remhash m minfo))
    (dolist (opinfo (module-all-operators module))
      (setf (opinfo-methods opinfo)
	    (delete-if #'(lambda (x)
			   (and (method-is-error-method x)
				(not (method-is-user-defined-error-method x))))
		       (opinfo-methods opinfo))))
    ))

;;;
;;; MAKE-OPERATOR-CLUSTERS-IN
;;;
(defun make-operator-clusters-in (&optional (module (or *current-module*
							*last-module*)))
  (declare (type module module)
	   (values t))
  (let ((result nil)
	(infos (module-all-operators module))
	(sort-order (module-sort-order module)))
    (when *on-operator-debug*
      (format t "~%**-- all operators in module: ")
      (print-chaos-object infos))
    (do* ((op-infos infos (cdr op-infos))
	  (info (car op-infos) (car op-infos)))
	((endp op-infos))
      (when (opinfo-methods info)
	(let ((proto-method nil)
	      (name nil)
	      (coar nil))
	  (setq proto-method
		(or (find-if #'(lambda (x) (method-is-universal* x))
			     (opinfo-methods info))
		    (find-if #'(lambda (x) (method-is-error-method x))
			       (opinfo-methods info))
		    (car (opinfo-methods info))))
	  (setq name (method-name proto-method))
	  (setq coar (method-coarity proto-method))
	  (when *on-operator-debug*
	    (format t "~%-- proto-method = ")
	    (print-chaos-object proto-method)
	    (format t "~%   name = ~s" name)
	    (format t "~%   coar = ")
	    (print-chaos-object coar))
	  (let ((pre (find-if #'(lambda (x)
				  (let ((m (car (opinfo-methods x))))
				    (and (equal (method-name m) name)
					 (or (equal name
						    '(("if" "_" "then" "_"
						       "else" "_" "fi")
						      . 3))
					     (is-in-same-connected-component
					      (method-coarity m)
					      coar
					      sort-order)))))
			      result)))
	    (if pre
		(progn
		  (when *on-operator-debug*
		    (let ((*print-indent* (+ 2 *print-indent*)))
		      (format t "~%** merging operators : ")
		      (print-next)
		      (princ "- pre = ")
		      (print-chaos-object pre)
		      (print-next)
		      (princ "- with : ")
		      (print-chaos-object info)))
		  (setf (opinfo-methods pre)
			(delete-duplicates 
			 (nconc (opinfo-methods pre)
				(opinfo-methods info))))
		  (when *on-operator-debug*
		    (let ((*print-indent* (+ 2 *print-indent*)))
		      (fresh-line)
		      (princ "-- the result : ")
		      (print-chaos-object pre)))
		  )
		(push info result))))))
    ;;
    (setf (module-all-operators module)
	  (nreverse result))))

;;; METHOD-SELECT-MOST-GENERAL-VERSION-OF
;;; used for computing method's syntactic properties for `simple-parser'.
;;; condition : largest arity and smallest coarity
;;;

(defun method-select-most-general-version-of (method methods
						     sort-order
						     &rest ignore)
					; opinfo-table
					; &optional mod
  (declare (ignore ignore)
	   (type method method)
	   (type list methods)
	   (type hash-table sort-order)
	   (values method))
  ;;
  (let ((res-method method))
    (dolist (meth2 methods)
      (when (or (and (method-is-universal meth2)
		     (method-is-of-same-operator res-method meth2))
		(method-is-instance-of res-method meth2 sort-order))
	(setq res-method meth2)))
    res-method))

;;; METHOD-MOST-GENERAL-NO-ERROR methd method-list module
;;;
(defun method-most-general-no-error (method methods
					    &optional
					    (module (or *current-module*
							*last-module*)))
  (declare (type method method)
	   (type list methods)
	   (type module module)
	   (values method))
  (let ((res-method method)
	(so (module-sort-order module)))
    (dolist (meth2 methods)
      (when (and (not (method-is-error-method meth2))
		 (method-is-instance-of res-method meth2 so))
	(setq res-method meth2)))
    res-method))
;;;
;;; SETUP-ERROR-OPERATORS-IN
;;; *NOTE* assumption : no error operators are generated in the module yet.
;;;
(defun get-new-error-sort-name-in (module sort-name)
  (declare (type module module)
	   (type (or simple-string symbol) sort-name))
  #||
  (let ((err-sort (find-error-sort-in module sort-name)))
    (if err-sort
	(string (sort-name err-sort))
      sort-name))
  ||#
  module
  sort-name
  )

(defun setup-user-defined-error-operators-in (module)
  (dolist (decl (remove-duplicates (module-error-op-decl module)
				   :test #'equal))
    (eval-ast decl)))

(defun setup-error-operators-in (&optional (module (or *current-module*
						       *last-module*)))
  (declare (type module module)
	   (values t))
  (let ((all-error-operators nil))
    ;; first we create error operators explicitly declared by user
    (with-in-module (module)
      (dolist (eop-decl (module-error-op-decl module))
	(let ((proto-arity (%op-decl-arity eop-decl))
	      (proto-coarity (%op-decl-coarity eop-decl)))
	  (when *on-operator-debug*
	    (format t "~%[setup-error-operators-in]:BEFORE")
	    (format t "~&  arity=~s" proto-arity)
	    (format t "~&  coarity=~s" proto-coarity))
	  #||
	  (setq proto-arity
	    (mapcar #'(lambda (sref)
			(if (%is-sort-ref sref)
			    (let ((name (%sort-ref-name sref)))
			      (setf (%sort-ref-name sref)
				(get-new-error-sort-name-in module name)))
			  (get-new-error-sort-name-in module sref)))
		    proto-arity))
	  (if (%is-sort-ref proto-coarity)
	      (setf (%sort-ref-name proto-coarity)
		(get-new-error-sort-name-in module
					    (%sort-ref-name proto-coarity)))
	    (setq proto-coarity
	      (get-new-error-sort-name-in module proto-coarity)))
	  (setf (%op-decl-arity eop-decl) proto-arity)
	  (setf (%op-decl-coarity eop-decl) proto-coarity)
	  ||#
	  (when *on-operator-debug*
	    (format t "~%[setup-error-operators-in]: declaring user defind errr op")
	  (format t "~% by decl : ") (print-chaos-object eop-decl))
	(let ((res (declare-operator eop-decl t)))
	  (if (null res)
	      (with-output-chaos-error ('invalid-op-decl)
		(format t "could not define error operator : ")
		(print-next)
		(print-ast res)
		)
	      (push res all-error-operators))))))
    ;; then, generates implicit ones. 
    (dolist (opinfo (module-all-operators module))
      (setq all-error-operators
	    (nconc all-error-operators
		   (setup-error-operator opinfo module))))
    (setf (module-error-methods module) all-error-operators)))

(defun setup-error-operator (opinfo module)
  (declare (type list opinfo)
	   (type module module)
	   (values t))
  (when *on-operator-debug*
    (format t "~%[generate-err-op]: ")
    (print-chaos-object (car opinfo)))

  ;; avoid generate if there already ...

  ;;#||
  (when (some #'(lambda (x)
		  (method-is-error-method x))
	      (opinfo-methods opinfo))
    (when *on-operator-debug*
      (format t "~% * already exists"))
    (return-from setup-error-operator nil))
  ;;||#
  ;;
  (let ((method-info-table (module-opinfo-table module))
	(sort-order (module-sort-order module))
	(pre-errs (module-error-methods module))
	(all-errs nil)
	)
    ;; NOTE:
    ;; all coarities of methods are in the same connected component.
    (let ((proto-method nil)
	  (method-name nil)
	  (err-coarity nil)
	  (new-arities nil)
	  (coherent nil)
	  )
      ;;
      (setq proto-method
	    (find-if #'(lambda (x) (method-is-universal* x))
		     (opinfo-methods opinfo)))
      (unless proto-method
	(setq proto-method (car (opinfo-methods opinfo))))

      ;; dont need error method for constants. <-- why?
      (unless (method-arity proto-method)
	(when (or (module-is-theory module)
		  (module-is-regular module))
	  (return-from setup-error-operator nil)))
      ;;
      (setq method-name (method-name proto-method))
      (setq err-coarity (the-err-sort (method-coarity proto-method)
				      sort-order))
      (unless err-coarity
	(with-output-panic-message ()
	  (format t "setup error operator: error sort of ")
	  (print-sort-name (method-coarity proto-method))
	  (format t " is not yet prepared!.")
	  (format t "~& object=~s" (method-coarity proto-method))
	  (format t "~%  so=~s" sort-order)
	  (pp-sort-order sort-order)))
      (when *on-operator-debug*
	(format t "~% * proto-method = ")
	(print-chaos-object proto-method)
	(format t "~% * err-coarity = ")
	(print-sort-name err-coarity module))
      
      (dolist (meth (opinfo-methods opinfo))
	(block next-method
	  (when (method-is-universal* meth)
	    (return-from next-method nil)) ; skip universal
	  (let ((coarity (method-coarity meth)))
	    (when (or (sort= coarity *universal-sort*)
		      (sort= coarity *huniversal-sort*)
		      (sort= coarity *cosmos*)
		      (sort= coarity *bottom-sort*))
	      (return-from next-method nil))
	    (let ((ar (mapcar #'(lambda (x)
				  (the-err-sort x sort-order))
			      (method-arity meth))))
	      (pushnew ar new-arities :test #'equal))
	    (setq coherent
		  (or coherent (method-is-coherent meth)))
	    )))
      (dolist (arity new-arities)
	(when *on-operator-debug*
	  (format t "~% * try for arity ")
	  (print-sort-list arity module))
	(let ((pre (find-if #'(lambda (x)
				(and (equal method-name
					    (method-name x))
				     (sort-list= arity
						 (method-arity x))
				     (sort= err-coarity
					    (method-coarity x))))
			    pre-errs)))
	  (if pre
	      ;; we already have error-method imported.
	      ;; just resuse this.
	      (progn
		(when *on-operator-debug*
		  (format t "~% * found pre defined ")
		  (print-chaos-object pre))
		(push pre all-errs)
		(add-method-to-table-very-fast opinfo pre module)
		;; we must generate new opinfo always.
		(setf (get-method-info pre method-info-table)
		      (make-method-info pre
					module
					(opinfo-operator opinfo)))
		(setf (method-theory pre method-info-table)
		      *the-empty-theory*)
		;; there can be axioms for pre-defined methods.
		;;
		(unless (eq (method-module pre) module)
		  (let ((from-opinfo (module-opinfo-table
				      (method-module pre)))
			(to-opinfo (module-opinfo-table module))
			(all-rules (module-all-rules module)))
		    (dolist (r (reverse (method-rules-with-different-top
					 pre
					 from-opinfo)))
		      (when (or (not (memq r all-rules))
				(eq pre (term-head (axiom-lhs r))))
			(add-rule-to-method (check-axiom-error-method module r)
					    pre
					    to-opinfo)
			(pushnew r (module-all-rules module)
				 :test #'rule-is-similar?)))))
		;;
		(compute-method-theory-info-for-matching
		 pre
		 method-info-table)
		(setf (method-is-coherent pre) coherent)
		)
	      ;; not yet have, generate a new one.
	      (multiple-value-bind (ent? meth)
		  (add-operator-declaration-to-table opinfo
						     arity
						     err-coarity
						     module
						     nil
						     nil
						     nil)
		(when *on-operator-debug*
		  (format t "~% * generatd new: ")
		  (print-chaos-object meth)
		  (format t "~%   -- entered? ~a" ent?))
		(when ent?
		  ;;
		  (push meth all-errs)
		  (setf (method-theory meth method-info-table)
			*the-empty-theory*
			(method-is-behavioural meth)
			(method-is-behavioural proto-method))
		  (setf (method-is-coherent meth) coherent)
		  (compute-method-theory-info-for-matching
		   meth method-info-table)
		  )))
	      ))
      ;; returns the list of error operators.
      all-errs)))

(defun make-sem-relation-op (module meth arity coarity)
  (declare (type module module)
	   (type method meth)
	   (type list arity)
	   (type sort-struct coarity)
	   (values t))
  (with-in-module (module)
    (multiple-value-bind (op new-meth)
	(declare-operator-in-module (operator-symbol (method-operator meth))
				    arity
				    coarity
				    module)
      (declare (ignore op))
      ;;
      (setf (method-constructor new-meth)
	    (method-constructor meth))
      (setf (method-is-behavioural new-meth)
	    (method-is-behavioural meth))
      (setf (method-supplied-strategy new-meth)
	    (method-supplied-strategy meth))
      (setf (method-precedence new-meth)
	    (method-precedence meth))
      (setf (method-associativity new-meth)
	    (method-associativity meth))
      (setf (method-theory new-meth)
	    (method-theory meth))
      (setf (method-theory-info-for-matching new-meth)
	    (method-theory-info-for-matching meth))
      )))

(defun make-if-then-else-op (module sort)
  (declare (type module module)
	   (type sort-struct sort)
	   (values t))
  (with-in-module (module)
    (multiple-value-bind (op new-meth)
	(declare-operator-in-module (operator-symbol *bool-if*)
				    (list *bool-sort* sort sort)
				    sort
				    module)
      (declare (ignore op))
      ;;
      (setf (method-constructor new-meth)
	    (method-constructor *bool-if*))
      (setf (method-is-behavioural new-meth)
	    (method-is-behavioural *bool-if*))
      (setf (method-supplied-strategy new-meth)
	    (method-supplied-strategy *bool-if*))
      (setf (method-precedence new-meth)
	    (method-precedence *bool-if*))
      (setf (method-associativity new-meth)
	    (method-associativity *bool-if*))
      (setf (method-theory new-meth)
	    (method-theory *bool-if*))
      (setf (method-theory-info-for-matching new-meth)
	    (method-theory-info-for-matching *bool-if*))
      )))
  
(defun setup-if-then-else-in (module)
  (declare (type module module)
	   (values t))
  (when (assq *truth-module* (module-all-submodules module))
    (let ((sorts (get-module-top-sorts module)))
      (dolist (es sorts)
	(make-if-then-else-op module es)))))
    
#||
(defun setup-sem-relations-in (module)
  (when (assq *truth-module* (module-all-submodules module))
    (let ((sorts (get-module-top-sorts module)))
      (dolist (es sorts)
	(if (sort-is-hidden es)
	    (progn
	      ;; _=*=_
	      (make-sem-relation-op module
				    *beh-equal*
				    (list es es)
				    *bool-sort*)
	      ;; _=b=_
	      (make-sem-relation-op module
				    *beh-eq-pred*
				    (list es es)
				    *bool-sort*))
	    (progn
	      ;; _==_
	      (make-sem-relation-op module
				    *bool-equal*
				    (list es es)
				    *bool-sort*)
	      ;; _=/=_
	      (make-sem-relation-op module
				    *bool-nonequal*
				    (list es es)
				    *bool-sort*)
	      ))
	)))
  (when (assq *rwl-module* (module-all-submodules module))
    ;; _==>_
    (let ((sorts (get-module-top-sorts module)))
      (dolist (s sorts)
	(make-sem-relation-op module
			      *rwl-predicate*
			      (list s s)
			      *bool-sort*))))
  )

||#

(defun setup-sem-relations-in (module)
  (declare (type module module)
	   (values t))
  (when (assq *truth-module* (module-all-submodules module))
    (let ((sorts (get-module-top-sorts module)))
      (dolist (es sorts)
	(if (sort-is-hidden es)
	    ;; _=*=_
	    (make-sem-relation-op module
				  *beh-equal*
				  (list es es)
				  *bool-sort*)
	    )))))

(defparameter memb-predicate-name-template
  '("_" ":" 'sort-name))

(defparameter memb-predicate-decl-template
  '(%opdecl name arity (%sort-ref "Bool" nil)
            (%opattrs nil nil 125 (1 2 0) nil nil nil)
    nil))

(defun make-sort-memb-decl-form (sort)
  (let ((name (string (sort-id sort)))
	(pred-name (copy-tree memb-predicate-name-template))
	(decl-form (copy-tree memb-predicate-decl-template)))
    (setf (third pred-name) name)
    (setf (second decl-form) pred-name)
    (setf (third decl-form)
	  (list (%sort-ref* (concatenate 'string "?" name) nil)))
    decl-form))

(defun declare-sort-memb-predicates (module)
  (dolist (s (module-sorts module))	; only for own sorts, others should be
					; imported.
    (let ((decl-form (make-sort-memb-decl-form s)))
      (pushnew decl-form (module-error-op-decl module)
	       :test #'equal))))

(defun declare-sort-id-constants (module)
  (when (memq *sort-id-sort* (module-all-sorts module))
    (dolist (sort (module-sorts module))
      (let ((op-name (list (string (sort-id sort)))))
	(unless (find-method-in module op-name nil *sort-id-sort*)
	  (declare-operator-in-module op-name
				      nil
				      *sort-id-sort*
				      module
				      t	; constructor
				      ))))))

(defun setup-operators-in (module)
  (declare (type module module)
	   (values t))
  (with-in-module (module)
    (let ((method-info-table (module-opinfo-table module))
	  (sort-order (module-sort-order module)))
      (flet ((compute-lower-methods (method methods &aux (meth-list nil))
	       (dolist (m methods)
		 (when (method-is-restriction-of m method sort-order)
		   (push m meth-list)))
	       (let ((res (topo-sort meth-list #'method-is-restriction-of)))
		 res)
	       )
	     (compute-overloaded-methods (method  methods &aux (meth-list nil))
	       (dolist (m methods)
		 (when (method-is-in-same-component method m sort-order)
		   (push m meth-list)))
	       ;;*** NOTE *** overloaded method is sorted
	       ;;                   lower -> higher
	       (nreverse (topo-sort meth-list #'method<))))
	;;
	(dolist (opinfo (module-all-operators module))
	  (let ((op (opinfo-operator opinfo))
		(methods (opinfo-methods opinfo)))
	    ;;
	    ;; compute default values of attributes for operator (not methods).
	    ;; 
	    (when (or (eq (operator-module op) *current-module*)
		      (null (operator-computed-precedence op)))
	      (setf (operator-computed-precedence op)
		    (compute-operator-precedence op))
	      (unless (operator-associativity op)
		(if (operator-is-associative op)
		    (setf (operator-associativity op)
			  :right)))
	      )
	    ;; set (1) lowers and highers,
	    ;;     (2) memo property
	    ;;     (3) match theory.
	    ;; (2) and (3) are module independent,
	    ;;     thus we compute these only for methods of
	    ;; current-module. imported methods already has these values
	    ;; set properly.
	    (let (;; (strat (operator-strategy op))
		  ;; strategy must be computed later.
		  (theory (operator-theory op)))
	      (dolist (m methods)
		(setf (method-lower-methods m)
		      (compute-lower-methods m methods))
		(setf (method-overloaded-methods m)
		      (compute-overloaded-methods m methods))
		(when (eq (method-module m) *current-module*)
		  #||
		  ;; (2) memo is now obsolete
		  (unless (method-has-memo m)
		    (setf (method-has-memo m) memo))
		  ||#
		  ;; ** the rewrite strategy for default methods are always eager.
		  ;;     we set the value here.
		  (when (method-is-error-method m)
		    (setf (method-rewrite-strategy m)
			  (the-default-strategy (operator-num-args op))))
		  
		  ;; (3) equational theory
		  (unless (method-is-error-method m)
		    (let ((m-th (method-theory m method-info-table)))
		      (if (and m-th (not (eq m-th *the-empty-theory*)))
			  (progn
			    ;; we take logical or
			    (setf (theory-info m-th)
				  (theory-code-to-info (logior (theory-code theory)
							       (theory-code m-th))))
			    ;;
			    (if (theory-zero theory)
				(setf (theory-zero m-th)
				      (theory-zero theory))))
			  ;; set the default value inherited from operator.
			  (progn
			    (setf (method-theory m method-info-table) theory)
			    (compute-method-theory-info-for-matching
			     m
			     method-info-table))
			  ))
		    ))
		))
	    
	    ;; setup method lookup table.
	    ;; *** NOT USED NOW ***
	    ;; (setf (opinfo-method-table opinfo)
	    ;;       (make-method-table (opinfo-methods  opinfo)
	    ;;                           *current-sort-order*))
	    ;;
	    #||
	    ;; compute syntactic properties for each methods.
	    (compute-method-syntactic-properties opinfo method-info-table)
	    ;; set syntactic properties for error methods.
	    (compute-error-method-syntactic-properties opinfo
						       method-info-table)
	    ||#
	    ))
	))))

(defun set-operator-syntactic-properties (module)
  (with-in-module (module)
    (let ((method-info-table (module-opinfo-table module)))
      (dolist (opinfo (module-all-operators module))
	  ;; compute syntactic properties for each methods.
	  (compute-method-syntactic-properties opinfo method-info-table)
	  ;; set syntactic properties for error methods.
	  (compute-error-method-syntactic-properties opinfo
						     method-info-table)
	  ))))

(defun make-standard-token-seq (op-name-token number-of-args)
  (declare (type fixnum number-of-args)
	   (values list))
  (if (zerop number-of-args)
      op-name-token
      (let ((res nil))
	(push "(" res)
	(dotimes (x number-of-args)
	  (push t res)
	  (if (< x (1- number-of-args))
	      (push "," res)))
	(push ")" res)
	(append op-name-token (nreverse res)))))

(defun compute-method-syntactic-properties (opinfo
					    method-info-table)
  (declare (type list opinfo)
	   (type hash-table method-info-table)
	   (values t))
  ;; here we construct a info about form of terms, 
  ;; used by our bottom up term parser.
  ;; 
  ;; ** how can we manipulate variable length arguments?
  ;;    any smart ways?
  (let* ((op (opinfo-operator opinfo))
	 (methods (opinfo-methods opinfo))
	 (op-prec (operator-computed-precedence op))
	 (op-assoc (operator-associativity op))
	 (token-sequence (operator-token-sequence op))
	 )
    (unless (operator-is-mixfix op)
      ;; operator has a standard application form.
      (setf token-sequence (make-standard-token-seq token-sequence
						    (operator-num-args op))))
    ;; NOTE : if we do not allow overloaded methods to have different syntactic
    ;;        properties, things will be very simple. to be considered.
    ;;
    (dolist (method methods)
      (let* ((prec (or (method-precedence method) op-prec))
	     (lower-prec (if (zerop prec)
			     0
			     (1- prec)))
	     (assoc-decl (or (method-associativity method)
			     (setf (method-associativity method)
				   ;; assoc theory is interpreted as right-associative
				   (if (and (method-is-associative method
								   method-info-table)
					    (null op-assoc)
					    )
				       ':right
				       op-assoc)))))
	(declare (type fixnum prec lower-prec)
		 (type symbol assoc-decl))
	;;
	(let* ((arity-list (method-arity method))
	       (cur-item nil)
	       (last-item nil)
	       (next-item nil)
	       (form nil)
	       (res nil)
	       (token-seq token-sequence)
	       (gathering (compute-gathering method token-seq assoc-decl)))
	  (declare (type list arity-list res token-seq gathering form))
	  ;;
	  (loop (when (null token-seq)
		  (setq form (nreverse res))
		  (return))
		(setq last-item cur-item)
		(setq cur-item (car token-seq))
		(setq next-item (cadr token-seq))
		(cond ((eq t cur-item)
		       (push (list* 'argument
				    (if (eq '& (car gathering))
					parser-max-precedence
					(if (and last-item
						 (not (eq t last-item))
						 next-item
						 (not (eq t next-item)))
					    parser-max-precedence
					    (if (eq ':right (car gathering))
						lower-prec
						(if (eq ':left (car gathering))
						    prec
						    0))))
				    (car arity-list))
			     res)
		       (setq arity-list (cdr arity-list)
			     gathering (cdr gathering)))
		      (t (push (cons 'token cur-item) res)))
		(setq token-seq (cdr token-seq)))
	  ;;
	  ; (terpri)
	  ; (print-chaos-object method)
	  ; (format t " :form= ~S" form)
	  ;;
	  (setf (method-form method) form))))))

(defun compute-error-method-syntactic-properties (opinfo method-info-table)
  (declare (type list opinfo)
	   (type hash-table method-info-table)
	   (values t))
  (dolist (meth (opinfo-methods opinfo))
    (when (method-is-error-method meth)
      (let ((ms (method-lower-methods meth method-info-table)))
	;; assumption, lower methods (when the mehthod is strictly
	;; overloaded) are ordered ...
	(when ms
	  (let ((assoc (method-associativity (car ms)))
		(prec (get-method-precedence (car ms) method-info-table))
		(form (method-form (car ms))))
	    (setf (method-associativity meth) assoc)
	    (setf (method-precedence meth) prec)
	    (setf (method-form meth)
		  (compute-error-method-form meth form))))))))

(defun compute-error-method-form (method form)
  (declare (type method method)
	   (type list form)
	   (values list))
  (let ((new-form nil)
	(arg-num 0)
	(arity (method-arity method)))
    (dolist (elt form)
      (if (eq (car elt) 'argument)
	  (progn
	    (push (cons (car elt)
			(cons (second elt)
			      (nth arg-num arity)))
		  new-form)
	    (incf arg-num))
	  (push elt new-form)))
    (nreverse new-form)))

(defun compute-gathering (method token-seq assoc-decl)
  (declare (type method method)
	   (type list token-seq)
	   (type symbol assoc-decl)
	   (values list))
  ;;
  ; (terpri)
  ; (print-chaos-object method)
  ; (format t " : assoc=~S" (method-is-associative method))
  ;;
  (if assoc-decl
      (if (eq assoc-decl ':left)
	  '(:left :right)
	  '(:right :left))
      ;; if unary prefix use :left not :right
      (if (not (operator-is-mixfix (method-operator method)))
	  (mapcar #'(lambda (x) (declare (ignore x)) '&) (method-arity method))
	  (if (and (eq t (car (last token-seq)))
		   (not (member t (butlast token-seq))))
	      '(:left)
	      (if (method-is-associative method)
		  '(:right :left)
		  (mapcar #'(lambda (x) (declare (ignore x)) ':left)
			  (method-arity method)))))))

;;;
;;; CHECK-POLIMORHIC-OVERLODING-IN
;;;
(defun check-polimorphic-overloading-in (&optional (module (or *current-module*
							    *last-module*)))
  (declare (type module module)
	   (values t))
  (with-in-module (module)
    (dolist (opinfo (module-all-operators module))
      (unless (methods-strictly-overloading (opinfo-methods opinfo))
	(dolist (m (opinfo-methods opinfo))
	  (setf (method-strictly-overloaded m) nil))))))

(defun methods-strictly-overloading (methods)
  (declare (type list methods)
	   (values (or null t)))
  (do* ((ms methods (cdr ms))
	(method (car ms) (car ms)))
       ((endp ms) t)
    (unless (every #'(lambda (x)
		       (or (method-is-restriction-of method
						     x
						     *current-sort-order*)
			   (method-is-restriction-of x
						     method
						     *current-sort-order*)))
		   ms)
      (return-from methods-strictly-overloading nil))))

;;; ********************
;;; FINAL SETUP ROUTINES________________________________________________________
;;; ********************

;;; setup procs for rewriting.

;;; The strategy of any operator is computed according to
;;; the following rules:
;;; 1/ "==" is a built-in operator with strategy (1 2 0).
;;; 2/ "if_then_fi" is a built-in operator with strategy (1 0 2).
;;; 3/ "if_then_else_fi" is a built-in operator with strategy (1 0 2 3).
;;; 4/ other built-in operators have strategy bottom-up, i.e. (1 ... n 0)
;;;    except if specified
;;; 5/ a. free constants (including built-in constants) have strategy nil.
;;;    b. non-free constants have strategy (0).
;;; 6/ "free constructors", i.e. operators that have no rule (but may have
;;;    built-in properties such as commutativity) have strategy (1 ... n).
;;; 7/ Other "ac" operators have strategy (1 ... n 0). @@ why? (ck)
;;; 8/ "operators that have no "rules with different top" are considered
;;;    to be "non free constructors" with bottom up strategy (1 ... n 0).
;;; 9/ All other operators have their strategy computed by the following
;;;    function that returns a permutation of 
;;;    [1 .. n] with some additional inserted Zeros:

;;; Z: We suppose that ALL the information relative to the operator are
;;;    entered when we compute the strategy. In particular all the rules
;;;    relative to this operator must be entered.
 
;;; the default rewrite strategy is leftmost-innermost.

(defun the-default-strategy (num-args)
  (declare (type fixnum num-args)
	   (values list))
  (case num-args
    (0 '(0))
    (1 '(1 0))
    (2 '(1 2 0))
    (3 '(1 2 3 0))
    (4 '(1 2 3 4 0))
    (5 '(1 2 3 4 5 0))
    (6 '(1 2 3 4 5 6 0))
    (t (let ((res nil))
	 (dotimes (x num-args) (declare (type fixnum x )) (push (1+ x) res))
	 (nreverse (cons 0 res))))))

(defun complete-method-strategy (meth strat)
  (declare (ignore meth)
	   (type list strat)
	   (values list))
  (if (and strat (not (eql (car (last strat)) 0)))
      (append strat '(0))
      strat))

(defun compute-rew-strategy (mod opinfo)
  (declare (type module mod)
	   (type list opinfo)
	   (values list))
  (with-in-module (mod)
    (let ((op (opinfo-operator opinfo))
	  (methods (opinfo-methods opinfo)))
      (dolist (meth methods)
	;; first inherits operator's strategy
	(unless (method-supplied-strategy meth)
	  (setf (method-supplied-strategy meth) (operator-rewrite-strategy op)))
	;; if the strategy is specified by the user, we don't modify it
	;; this covers in particular cases 1, 2, 3, 4
	;; 
	(when (method-supplied-strategy meth)
	  (setf (method-rewrite-strategy meth)
		;; patch: use supplied strategy as is.
                ;; (complete-method-strategy meth (method-supplied-strategy meth))		
		(method-supplied-strategy meth)))
	
	;; compute strategy
	(unless (method-rewrite-strategy meth)
					; this condition also covers the
					; case of default method.
	  (cond ((and (null (method-rules-with-different-top meth))
		      (rule-ring-is-empty (method-rules-with-same-top meth)))
		 ;; the method has no rewrite rules
		 ;; --> cases 5.a and 6: the operator is free from axioms.
		 ;; *NOTE* complete-method-strategy is not neccessary here.
		 ;; *also* the-default-strategy returns nil when num-args = 0 .
		 (setf (method-rewrite-strategy meth)
		   ; (butlast (the-default-strategy (operator-num-args op)))
		   (the-default-strategy (operator-num-args op))))
		
		;; the method has some rewrite rules associated with it.
		((or
		  ;; case 7 : has some equational theory
		  (not (theory-is-empty-for-matching (method-theory meth)))
		  ;; case 8 : the method is not free constructor.
		  (null (method-rules-with-different-top meth))
		  ;; case 5.b : has rules with different top and constant
		  ;; --> non-free constructor
		  (null (method-arity meth)))
		 ;; then the strategy is bottom up:
		 (setf (method-rewrite-strategy meth)
		       (the-default-strategy (operator-num-args op))))
		
		(t
		 ;; case 9: the real work begins here.
		 ;; this is a rather huristic optimization of reduction process.
		 ;; the 
		 (let ((strategy nil)
		       (end-strategy nil)
		       (l-ar (operator-num-args op)))
		   (declare (type fixnum l-ar))
		   (do ((occ 0 (1+ occ)))
		       ((<= l-ar occ))
		     (declare (type fixnum occ))
		     (block is-variable
		       (let ((rr  (method-rules-with-same-top meth)))
			 (do ((rule (initialize-rule-ring rr) (rule-ring-next rr)))
			     ((end-of-rule-ring rr))
			   (unless (term-is-variable?
				    (term-arg-n (rule-lhs rule) occ))
			     ;; we eagarly evaluate non-variable argument.
			     (push (1+ occ) strategy)
			     ;; check next argument
			     (return-from is-variable))))
		       ;; we come here iff
		       ;; the arguments in lhs of all rules-with-same-top are
		       ;; variables or no rules-with-same-top.
		       (dolist (rule (method-rules-with-different-top meth))
			 (When
			     (let ((argn (term-arg-n (rule-lhs rule) occ))
				   (m (term-head (rule-lhs rule))))
			       (or (not (term-is-variable? argn))
				   ;; argn is not a variable.
				   (rule-is-builtin rule)
				   (not (and
					 ;; method is maximal?
					 ;; overloaded is necessarily a superset
					 ;; of lower. Note, overloaded always include
					 ;; self + default method, but lower not.
					 ;; thus #lower = #overloaded - 2 means the
					 ;; method is maximal.
					 (= (length (method-lower-methods meth))
					    (- (length (method-overloaded-methods meth)) 2))
					 (sort<= (nth occ (method-arity m))
						 (term-sort argn))
					 ))))
			   ;; method of lhs is not maximal,
			   ;; eagarly evaluates the non-variable argument.
			   (push (1+ occ) strategy)
			   ;; check the next arg.
			   (return-from is-variable)))
		       ;; come here if the occ-th argument is a variable,or
		       ;; method is maximal. delay the evaluation.
		       (push (1+ occ) end-strategy)
		       ))
		   (setf (method-rewrite-strategy meth)
                         (complete-method-strategy meth
			                           (append (reverse strategy)
				                           (if (member 0 strategy) nil '(0))
				                           (reverse end-strategy))))
		   ))))))))

;;; *NOTE* assumes *current-opinfo-table* is properly bound.
;;;
(defun fix-strategy-and-rules (module opinfo)
  (declare (type module module)
	   (type list opinfo)
	   (values t))
  (with-in-module (module)
    (dolist (mth (opinfo-methods opinfo))
      (let ((rr (method-rules-with-same-top mth)))
	(when (method-supplied-strategy mth)
	  (unless (eql 0 (car (method-supplied-strategy mth)))
	    (when *on-operator-debug*
	      (princ "- merging rewrite rules of ")
	      (print-chaos-object mth))
	    (let ((rwst (rule-ring-to-list rr)))
	      (setf (method-rules-with-different-top mth)
		    (append rwst (method-rules-with-different-top mth)))
	      (setf (rule-ring-ring rr) nil))))
	;;
	(setf (method-rules-with-different-top mth)
	      (sort (method-rules-with-different-top mth) 
		    #'method<=
		    :key #'(lambda (x) (term-head (axiom-lhs x)))))
	;;
	))))

(defun propagate-attributes (module)
  (declare (type module module)
	   (values t))
  (let ((opinfos (module-all-operators module)))
    (with-in-module (module)
      (dolist (opinfo opinfos)
	(dolist (m (opinfo-methods opinfo))
	  ;; for each operator methods
          (unless (method-is-error-method m)
            (let* ((lower-ops (method-lower-methods m))
                   (p-theory (method-theory m))
                   (code (theory-info-code (theory-info p-theory)))
                   (id (car (theory-zero p-theory)))
                   (no-compl (if (cdr (theory-zero p-theory)) t nil)))
	      (declare (type fixnum code))
	      ;;
	      ;; check with lower operators of m
	      ;;   p-theory : theory of method m
	      ;;   code     : theory code of method m
	      ;;   id       : zero for p-theory if any
              (dolist (lower lower-ops)
                (when (method-is-restriction-of lower m)
		  ;; seems this test is redundant...
                  (let ((othy (method-theory lower))
                        newthy)
		    ;; othy : theory of lower method 
                    (setq code (logior code (theory-info-code (theory-info othy))))
		    ;; code now inherits super.
		    (when (theory-zero othy)
		      ;; reset id if lower method has its own.
		      (setq id (car (theory-zero othy))))

		    ;; check with other overloading methods.
		    (dolist (anop lower-ops)
		      (when (method-is-restriction-of lower anop)
			(let ((thy (method-theory anop)))
			  (when (theory-contains-associativity thy)
			    (setq code (logior code .A.)))
			  (when (theory-contains-commutativity thy)
			    (setq code (logior code .C.)))
			  (when (theory-contains-idempotency thy)
			    (setq code (logior code .I.)))
			  (when (theory-contains-identity thy)
			    (setq code (logior code .Z.))
			    (when (cdr (theory-zero thy))
			      (setq no-compl t))
			    (if (null id)
                                (setq id (car (theory-zero thy)))
                                (let ((nid (car (theory-zero thy))))
                                  (when (and nid (not (term-is-congruent? id nid)))
                                    (with-output-chaos-warning ()
                                      (princ "different possible identities for operator ")
                                      (print-chaos-object (opinfo-operator opinfo))
				      (print-next)
				      (term-print id) (princ " -- VS. -- ")
				      (term-print nid)))
                                  )))
			  )))
		    ;;
		    (when id
		      (let ((idsrt (term-sort id))
			    (ar (method-arity lower)))
			(when (not (or (sort<= idsrt (car ar))
				       (sort<= idsrt (cadr ar))))
			  ;; (break)
			  (setq code (logxor code .Z.))
			  (setq id nil))))
		    ;;
		    (setf newthy
			  (create-theory code
					 (when id
					   (cons id no-compl))))
		    (when (and no-compl
			       (theory-zero othy)
			       (not (cdr (theory-zero othy))))
		      (with-output-chaos-warning ()
			(princ "variation in id completion")
			(princ " for ") (print-chaos-object m)))
		    ;;
		    (set-method-theory lower
				       newthy
				       #|| set-method-theory calls this
				       (check-method-theory-consistency
					      lower
					      newthy
					      *current-opinfo-table*
					      t)
				       ||#
				       *current-opinfo-table*
				       t))
		    ))
	      ))			; end unless
	  )				; end dolist
	)				; end dolist
      )
    ))


;;; EOF
