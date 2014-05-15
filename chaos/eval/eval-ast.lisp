;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: eval-ast.lisp,v 1.11 2010-07-13 02:12:59 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				  Module: eval
			      File: eval-ast1.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ** DESCRIPTION =============================================================
;;; Evaluators of ASTs of basic Chaos language constructs.
;;;

;;; ** Common interface:********************************************************
;;;  input  : abstract syntax tree.
;;;  output : corresponding semantic object, or nil will be returned if the
;;;           evaluation  process failed.
;;; ****************************************************************************

;;;=============================================================================
;;;		       SORT, SUBSORT, RECORD/CLASS SORTS
;;;=============================================================================

;;;-----------------------------------------------------------------------------
;;; DECLARE-SORT
;;; the evaluator of `sort-decl' : (%sort-decl sort-name)
;;;

;;; RESOLVE-SORT-REF : sort-name -> sort or nil
;;;     sort-name can be `sort-ref', symbol, or string
;;;     exception : strang-sort-name iff the `sort-name' is not
;;;                 in the above case.
(defun resolve-sort-ref (module sort-name)
  (cond ((%is-sort-ref sort-name)
	 (find-sort-in module sort-name))
	((or (symbolp sort-name)
	     (stringp sort-name))
	 (find-sort-in module sort-name))
	(t (with-output-chaos-error ('strange-sort-name)
	     (format t "internal error, strange sort name ~a" sort-name)
	     ))))

;;; RESOLVE-OR-DEFINE-SORT : sort-name -> sort
;;;     uses `resove-sort-ref' for referring existing sort,
;;;     if cound not find, declare new sort in the current context.
;;;
(defun resolve-or-define-sort (module sort-name &optional hidden)
  (let ((sort (resolve-sort-ref module sort-name)))
    (if sort
	(cond ((or (eq sort *universal-sort*)
		   (eq sort *huniversal-sort*)
		   ;;(eq sort *cosmos*)
		   )
	       (let ((*chaos-quiet* t))
 		 (declare (special *chaos-quiet*))
		 (with-output-chaos-error ('invalid-sort-decl)
		   (format t "You can not declare built in sort ~A"
			   (string (sort-name sort))))))
	      (t (if (or (and hidden (sort-is-hidden sort))
			 (and (not hidden) (not (sort-is-hidden sort))))
		     sort
		   (let ((*chaos-quiet* t))
		     (declare (special *chaos-quiet*))
		     (with-output-chaos-warning ()
		       (princ "declaring ")
		       (format t "a ~a sort ~s, there already be a sort" 
			       (if hidden
				   "hidden"
				 "visible")
			       (if (%is-sort-ref sort-name)
				   (%sort-ref-name sort-name)
				 sort-name))
		       (print-next)
		       (princ "with the same name but of different type (visible/hidden).")
		       (print-next)
		       (princ "...ignored.")
		       (return-from resolve-or-define-sort nil))
		     ))))
      (cond ((%is-sort-ref sort-name)
	       (if (%sort-ref-qualifier sort-name)
		   ;; should not happen this case.
		   (with-output-chaos-error ('invalid-sort-decl)
		     (princ "declare-sort accepted a qualified sort-name:")
		     (print-next)
		     (format t "sort name = ~s, qulifier = "
			     (%sort-ref-name sort-name))
		     (print-modexp (%sort-ref-qualifier sort-name))
		     (print-next)
		     (princ "ignoring the declaration.")
		     )
		   ;; 
		   (let ((true-name (%sort-ref-name sort-name)))
		     (declare-sort-in-module (if (stringp true-name)
						 (intern true-name)
						 true-name)
					     *current-module*
					     'sort
					     hidden))))
	      ((stringp sort-name)
	       (declare-sort-in-module (intern sort-name)
				       *current-module*
				       'sort
				       hidden))
	      ((symbolp sort-name)
	       (declare-sort-in-module sort-name
				       *current-module*
				       'sort
				       hidden))
	      (t (with-output-panic-message ()
		   (format t "declaring sort : accepted invalid name ~s" sort-name)
		   (break
		    "Please send bug report to \"sawada@sra.co.jp\", thanks~")))))
    ))

;;; DECLARE-SORT : sort-decl
;;;
(defun declare-sort (sort-decl)
  (I-miss-current-module declare-sort)
  (include-chaos-module)
  (set-needs-parse)
  (resolve-or-define-sort *current-module*
			  (%sort-decl-name sort-decl)
			  (%sort-decl-hidden sort-decl)))

;;; DECLARE-PSORT (psort-decl)
;;; real evaluation is postponed untill all sorts are visible in the module,
;;; so we set the declaration in the module.
;;;
(defun declare-psort (psort-decl)
  (I-miss-current-module declare-psort)
  (setf (module-psort-declaration *current-module*) psort-decl))

;;; and the following is the real evaluation proc.

(defun eval-psort-declaration (decl module)
  (let ((sort-ref (%psort-decl-sort decl))
	(sort nil))
    ;; we have a case the reference is just a sort-object,
    ;; occuring only when we inherit p-sort in instantiation/renaming.
    ;;
    (if (sort-p sort-ref)
	(setq sort sort-ref)
	(setq sort (resolve-sort-ref module (%psort-decl-sort decl))))
    (unless sort
      (with-output-chaos-error ('no-such-sort)
	(princ "declaring principal sort, no such sort ")
	(print-sort-ref (%psort-decl-sort decl))
	))
    (setf (module-principal-sort module) sort)))

;;;-----------------------------------------------------------------------------
;;; DECLARE-BSORT bsort-decl
;;; *NOTE* declare-bsort overrides previous declarations if any.
;;;
(defun declare-bsort (decl)
  (I-miss-current-module declare-bsort)
  (include-chaos-module)
  (set-needs-parse)
  (define-builtin-sort (%bsort-decl-name decl)
      *current-module*
    (list (%bsort-decl-token-predicate decl)
	  (%bsort-decl-term-creator decl)
	  (%bsort-decl-term-printer decl)
	  (%bsort-decl-term-predicate decl))
    (%bsort-decl-hidden decl)))

;;;-----------------------------------------------------------------------------
;;; DECLARE-SUBSORT subsort-decl
;;; the evaluator of `subosrt-decl' :
;;;   (%subsort-decl (%sort-ref ..) ((%sort-ref ...) ...))
;;; when success, the return value is a sort-order (the internal object for
;;; representing transitive closure of sort relations. ).
;;;
(defun declare-subsort (subsort-decl)
  (I-miss-current-module declare-subsort)
  ;; (set-needs-parse)
  (include-chaos-module)
  ;; save the declaration in unresoled form. NO MORE.
  ;; (push subsort-decl (module-sort-relations *current-module*))
  ;; call declare-subsort-in-module after resolving sort references.
  (let ((hidden (car (%subsort-decl-sort-relation subsort-decl)))
	(body (cdr (%subsort-decl-sort-relation subsort-decl))))
    (declare-subsort-in-module
     (list (mapcar #'(lambda (x)
		       (if (eq x ':<)
			   ':<
			   (resolve-or-define-sort *current-module* x hidden)))
		   body))
     *current-module*
     hidden )))

;;;-----------------------------------------------------------------------------
;;; DECLARE-RECORD
;;;
(defun declare-record (record-decl)
  (I-miss-current-module declare-record)
  (include-BOOL)
  (include-RECORD)
  (let ((rsort (declare-record-in-module *current-module*
					 (%record-decl-name record-decl)
					 (%record-decl-supers record-decl)
					 (%record-decl-attributes
					  record-decl)
					 (%record-decl-hidden record-decl))))
    (set-needs-parse)
    (set-needs-rule)
    rsort))

;;;-----------------------------------------------------------------------------
;;; DECLARE-CLASS
;;;
(defun declare-class (class-decl)
  (I-miss-current-module declare-class)
  (include-BOOL)
  (include-OBJECT)
  (let ((csort (declare-class-in-module *current-module*
					(%class-decl-name class-decl)
					(%class-decl-supers class-decl)
					(%class-decl-attributes class-decl)
					(%class-decl-hidden class-decl))))
    (set-needs-parse)
    (set-needs-rule)
    csort))

;;;=============================================================================
;;; 			 OPERATOR, OPERATOR ATTRIBUTES
;;;=============================================================================

;;; FIND-QUAL-OPERATORs : OpRef -> List[OpInfo]
;;;
(defun find-qual-operators (opref &optional mod (type nil))
  (let ((name (%opref-name opref))
	(num-args (%opref-num-args opref))
	(module (%opref-module opref)))
    (if module
	(let ((modval (eval-modexp module)))
	  (if (module-p modval)
	      (find-all-qual-operators-in modval name num-args type)
	      (with-output-chaos-error ('no-such-module)
		(princ "resolving operator reference ")
		(print-ast opref)
		(print-next)
		(princ "no such module ")
		(print-modexp module)
		)))
        (if mod
	    (find-all-qual-operators-in mod name num-args type)
	    (progn
	      (I-miss-current-module find-qual-operators)
	      (find-all-qual-operators-in *current-module* name num-args type))))))
    
;;; DECLARE-OPERATOR opdecl -> method
;;; returns method if success, otherwise nil.
;;;
(defun declare-operator (op-decl &optional error-operator)
  (I-miss-current-module declare-operator)
  (include-BOOL)
  (let* ((attr (%op-decl-attribute op-decl))
	 (memo (%opattrs-memo attr)	;(if (and *memo-rewrite* *always-memo*)
					; t
					;	 (%opattrs-memo attr))
	       )
	 (theory (%opattrs-theory attr))
	 (assoc (%opattrs-assoc attr))
	 (prec (%opattrs-prec attr))
	 (strat (%opattrs-strat attr))
	 (constr (%opattrs-constr attr))
	 (coherent (%opattrs-coherent attr))
	 (meta-demod (%opattrs-meta-demod attr)))
    (multiple-value-bind (op meth delayed)
	(declare-operator-in-module (%op-decl-name op-decl)
				    (%op-decl-arity op-decl)
				    (%op-decl-coarity op-decl)
				    *current-module*
				    constr
				    (%op-decl-hidden op-decl)
				    coherent
				    error-operator
				    )
      (when delayed
	(push op-decl (module-error-op-decl *current-module*))
	(mark-need-parsing-preparation *current-module*)
	(return-from declare-operator t))
      ;;
      (if (and op meth)
	  (progn
	    ;; memo attribute
	    (when memo
	      (declare-method-memo-attr meth memo)
	      )
	    ;; meta-demod predicate
	    (when meta-demod
	      (declare-method-meta-demod-attr meth meta-demod))
	    ;;
	    (if theory
		(declare-method-theory meth theory)
		(progn
		  (setf (method-theory meth *current-opinfo-table*)
			*the-empty-theory*)
		  (compute-method-theory-info-for-matching meth
							   *current-opinfo-table*)
		  ))
	    (when assoc
	      (if (eq (method-module meth)
		      *current-module*)
		  (declare-method-associativity meth assoc)
		  (with-output-chaos-warning ()
		    (princ "you cannot alter associativity of")
		    (print-next)
		    (princ "operator ")
		    (print-chaos-object meth)
		    (print-next)
		    (princ "of module ")
		    (print-simple-mod-name (method-module meth))
		    (print-next)
		    (princ "ignoring.."))))
	    (when prec
	      (if (eq (method-module meth) *current-module*)
		  (declare-method-precedence meth prec)
		  (with-output-chaos-warning ()
		    (princ "you cannot alter precedence of")
		    (print-next)
		    (princ "operator ")
		    (print-chaos-object meth)
		    (print-next)
		    (princ "of module ")
		    (print-simple-mod-name (method-module meth))
		    (print-next)
		    (princ "ignoring.."))))
	    (when strat
	      (if (eq (method-module meth) *current-module*)
		  (declare-method-strategy meth strat)
		  (with-output-chaos-warning ()
		    (princ "you cannot alter strategy of")
		    (print-next)
		    (princ "operator ")
		    (print-chaos-object meth)
		    (print-next)
		    (princ "of module ")
		    (print-simple-mod-name (method-module meth))
		    (print-next)
		    (princ "ignoring.."))))
	    ;; (when constr (declare-method-constr meth constr))
	    ;; (when coherent (declare-method-coherent meth coherent))
	    (set-needs-parse)
	    (set-needs-rule)
	    meth)
	nil))))

;;; DECLARE-OPERATOR-ATTRIBUTES : decl -> operator
;;; returns operator if success, otherwise nil.
;;;
#||
(defun declare-operator-attributes (decl)
  (I-miss-current-module declare-operator-attributes)
  ;; *NOTE* qualifier in opref is ignored, is it OK?
  (let ((name (%opref-name (%opattr-decl-opref decl)))
	(num-args (%opref-num-args (%opattr-decl-opref decl)))
	(attr (%opattr-decl-attribute decl)))
    (let ((opinfo (find-qual-operator-in *current-module* name num-args)))
      (unless opinfo
	(with-output-chaos-error ('operator-not-found)
	  (format t "declaring attributes, could not found unique operator ~a."
		  name)
	  ))
      (let ((op (opinfo-operator opinfo))
	    (memo (%opattrs-memo attr))
	    (theory (%opattrs-theory attr))
	    (assoc (%opattrs-assoc attr))
	    (prec (%opattrs-prec attr))
	    (strat (%opattrs-strat attr)))
	;; (when memo (declare-operator-memo-attr op memo))
	(when memo
	  (with-output-chaos-warning ()
	    (format t "memo attribute is now obsolate.")))
	(when theory (declare-operator-theory op theory))
	(when assoc (declare-operator-associativity op assoc))
	(when prec (declare-operator-precedence op prec))
	(when strat (declare-operator-strategy op strat))
	(set-needs-parse)
	(set-needs-rule)
	;; save the declaration form.
	(push decl (module-opattrs *current-module*))
	op))))
||#

;;;=============================================================================
;;;			       AXIOMS, VARIABLES
;;;=============================================================================

;;;-----------------------------------------------------------------------------
;;; DECLARE-VARIABLE
;;; evaluates variable-declaration form.
;;; 
(defun declare-variable (ast)
  (I-miss-current-module declare-variable)
  ;; (set-needs-parse) ; too early to set the flag.
  (include-BOOL)
  (let ((sort (find-sort-in *current-module* (%var-decl-sort ast)))
	(res nil))
    (unless sort
      (if (may-be-error-sort-ref? (%var-decl-sort ast))
	  (progn
	    ;; may be declaration of variable of error sorts.
	    (push ast (module-error-var-decl *current-module*))
	    (return-from declare-variable t))
	  ;;
	  (with-output-chaos-error ('no-such-sort)
	    (format t "declaring variable(s)~{~^ ~a~^,~},"
		    (%var-decl-names ast))
	    ;; (print-ast (%var-decl-sort ast))
	    (print-next)
	    (format t "no such sort: ~a" (%sort-ref-name (%var-decl-sort ast)))
	    )))
    (dolist (name (%var-decl-names ast))
      (push (declare-variable-in-module name sort *current-module*) res))
    ;; - patch, now we are safe to set the flag.
    (set-needs-parse)
    ;; 
    (nreverse res)))

(defun declare-pvariable (ast)
  (I-miss-current-module declare-pvariable)
  ;; (set-needs-parse) ; too early to set the flag.
  (include-BOOL)
  (let ((sort (find-sort-in *current-module* (%pvar-decl-sort ast)))
	(res nil))
    (unless sort
      (if (may-be-error-sort-ref? (%pvar-decl-sort ast))
	  (progn
	    ;; may be declaration of variable of error sorts.
	    (push ast (module-error-var-decl *current-module*))
	    (return-from declare-pvariable t))
	  ;;
	  (with-output-chaos-error ('no-such-sort)
	    (format t "declaring pseud variable(s)~{~^ ~a~^,~}, no such sort."
		    (%pvar-decl-names ast))
	    (print-ast (%pvar-decl-sort ast))
	    )))
    (dolist (name (%pvar-decl-names ast))
      (push (declare-pvariable-in-module name sort *current-module*) res))
    ;; - patch, now we are safe to set the flag.
    (set-needs-parse)
    ;; 
    (nreverse res)))

;;;-----------------------------------------------------------------------------
;;; DECLARE-AXIOM
;;; evaluates axiom declaration form.
;;; 

(defun is-lisp-form-token-sequence (token-list)
  (and (consp (car token-list))
       (memq (caar token-list) '(%slisp %glisp :slisp :glisp))))

(defun is-chaos-value-token-sequence (token-list)
  (and (consp (car token-list))
       (eq (caar token-list) '|%Chaos|)))

(defvar .special-meta-rule-labels. '(|:m-and| |:m-or|))

(defun declare-axiom (ast)
  (I-miss-current-module declare-axiom)
  ;; 
  (let* ((sort *cosmos*)
	 (*fill-rc-attribute* t)
	 (*parse-variables* nil)
	 (*parse-lhs-attr-vars* nil)
	 (*lhs-attrid-vars* nil)
	 (lhs (%axiom-decl-lhs ast))
	 (rhs (%axiom-decl-rhs ast))
	 (cond-part (%axiom-decl-cond ast))
	 (labels (%axiom-decl-labels ast))
	 (type (%axiom-decl-type ast))
	 (behavioural (%axiom-decl-behavioural ast))
	 (the-axiom nil)
	 (meta-and (member '|:m-and| labels))
	 (meta-or  (member '|:m-or| labels)))
    ;;
    (when (and meta-and meta-or)
      (with-output-chaos-error ('invalid-meta-rule)
	(format t "You cannot specify both :m-and and :m-or at once!")))
    ;;
    ;; (format t "~&labels=~s, meta-and=~s, meta-or=~s" labels meta-and meta-or)
    ;;
    (when (eq type :rule)
      (include-rwl *current-module*))
    (prepare-for-parsing *current-module*)
    ;;
    (cond ((or (is-lisp-form-token-sequence rhs)
	       (is-chaos-value-token-sequence rhs))
	   ;;
	   (when (or meta-and meta-or)
	     (with-output-chaos-error ('invalid-special-rule)
	       (format t "Invalid special rule ~s for built-in axiom." 
		       (if meta-and
			   ":m-and"
			 ":m-or"))))
	   ;; aka builtin rule.
	   (let* ((parsed-lhs (simple-parse *current-module* lhs sort))
		  (parsed-rhs (simple-parse *current-module* rhs sort))
		  (parsed-cnd (if cond-part
				  (simple-parse *current-module* cond-part sort)
				  *bool-true*))
		  (error-p nil))
	     (setf sort (term-sort parsed-lhs))
	     (when (and parsed-cnd (term-ill-defined parsed-cnd))
	       (with-output-simple-msg ()
		 (princ "[Error] no parse for condition part of the axiom."))
	       (setf error-p t))
	     ;;
	     (when (term-is-builtin-constant? parsed-lhs)
	       (with-output-chaos-error ('invlaid-lhs)
		 (format t "sole built-in constant on LHS is not allowed, sorry!")))
	     ;;
	     (if (or (term-ill-defined parsed-lhs)
		     (null sort))
		 (with-output-simple-msg ()
		   (princ "[Error] no parse for LHS of the axiom (ignored): ")
		   nil)
		 (if (not error-p)
		     (let ((canon (canonicalize-variables (list parsed-lhs parsed-rhs parsed-cnd) *current-module*)))
		       (setq the-axiom
			 (make-rule :lhs (first canon)
				    :rhs (second canon)
				    :condition (third canon)
				    :labels labels
				    :behavioural behavioural
				    :type type)))
		   (chaos-error 'invalid-axiom-decl) ))))
	  
	  ;; normal rule
	  (t (let* ((parses-lhs (let ((*parsing-axiom-lhs* t))
				  (parser-parses *current-module* lhs sort)))
		    (parses-rhs (parser-parses *current-module* rhs sort))
		    (parsed-cnd (if cond-part
				    (simple-parse *current-module*
						  cond-part
						  sort)
				    *bool-true*))
		    (error-p nil))
	       ;;
	       ;; check condition part.
	       ;;
	       (when (and cond-part (term-ill-defined parsed-cnd))
		 (with-output-simple-msg ()
		   (princ "[Error] no parse for axiom condition"))
		 (setf error-p t))
	       
	       ;; find apropreate pair of LHS & RHS.
	       (let ((res (parser-find-rule-pair
			   *current-module* parses-lhs parses-rhs)))
		 (if (null res)
		     ;; completely no found.
		     (with-output-simple-msg ()
		       (princ "[Error] bad axiom (ignored): ")
		       ;; show LHS 
		       (if (null parses-lhs)
			   (format t "~& No possible parse for LHS")
			   (progn
			     (format t "~&- LHS")
			     (dolist (f parses-lhs)
			       (print-next)
			       (print-term-tree f t))))
		       ;; show RHS
		       (if (null parses-rhs)
			   (format t "~& No possible parse for RHS")
			   (progn
			     (format t "~&- RHS")
			     (dolist (f parses-rhs)
			       (print-next)
			       (print-term-tree f t)
			       )))
		       (chaos-error 'invalid-axiom-decl))
		     ;;
		     (progn
		       (unless (null (cdr res))
			 (with-output-chaos-warning ()
			   (princ "axiom is ambiguous: ") (print-next)
			   (unless (null (cdr parses-lhs))
			     (princ "-- More than one parse for the LHS")
			     (print-next)
			     (format t "form : ~a" lhs)
			     (print-next)
			     (format t "trees:")
			     (parse-show-diff parses-lhs)
			     (format t "~&...adopting [1]..."))
			   (unless (null (cdr parses-rhs))
			     (princ "-- More than one parse for the RHS")
			     (print-next)
			     (format t "form : ~a" rhs)
			     (print-next)
			     (format t "trees:")
			     (parse-show-diff parses-rhs)
			     (format t "~&...adopting [1]..."))))
		       (if (not error-p)
			   (let ((lhs-result (car (car res)))
				 (rhs-result (parse-convert (cadr (car res)))))
			     
			     (when (term-is-builtin-constant? lhs-result)
			       (with-output-chaos-error ('invlaid-lhs)
				 (format t "sole built-in constant on LHS is not allowed, sorry!")
				 (print-ast ast)
				 ))
			     ;;
			     (when (or meta-and meta-or)
			       ;; lhs must be associative 
			       #||
			       (unless (method-is-associative (term-head lhs-result))
				 (with-output-chaos-error ('ivalid-lhs)
				   (format t "For :m-and/:m-or axioms, LHS must be of associative operator.")))
			       ||#
			       (unless (eq *bool-true* parsed-cnd)
				 (with-output-chaos-error ('invalid-cond)
				   (format t "Sorry, but now :m-and/:m-or can only be specified for non-conditional axioms.")))
			       (unless (is-in-same-connected-component *bool-sort* 
								       (term-sort rhs-result)
								       *current-sort-order*)
				 (with-output-chaos-error ('invalid-rhs)
				   (format t "RHS must be a term of sort Bool for :m-and/:m-or axiom."))))
			     ;;
			     (let ((canon (canonicalize-variables (list lhs-result rhs-result parsed-cnd) *current-module*)))
			       (setq the-axiom
				 (make-rule :lhs (first canon)
					    :rhs (second canon)
					    :condition (third canon)
					    :behavioural behavioural
					    :labels labels
					    :type type
					    :meta-and-or (if meta-and
							     :m-and
							   (if meta-or
							       :m-or
							     nil)))))
			     ;;
			     (when *chaos-verbose*
			       (when behavioural
				 (unless (and (term-can-be-in-beh-axiom?
					       lhs-result)
					      (term-can-be-in-beh-axiom?
					       rhs-result))
				   (with-output-chaos-warning ()
				     (format t "non-behavioural operation on hidden sorts appearing in the behavioural axiom:")
				     (with-in-module (*current-module*)
				       (print-next)
				       (print-chaos-object the-axiom)))))))
			   (chaos-error 'invalid-axiom-decl))))))))
    ;; check the axiom
    (check-axiom-error-method *current-module* the-axiom t)
    ;; additionaly if condition part contains match-op...
    (when (term-contains-match-op (axiom-condition the-axiom))
      (setf (axiom-contains-match-op the-axiom) t))
    ;; add to module: was add-axiom-to-module...
    (adjoin-axiom-to-module *current-module* the-axiom)
    ;; set module status
    (set-needs-rule)
    the-axiom))

;;;=============================================================================
;;; LET
;;;=============================================================================

(defun eval-let (ast)
  (let ((sym (%let-sym ast))
	(value (%let-value ast)))
    ;; (I-miss-current-module eval-let)
    (unless *current-module*
      (with-output-chaos-error ('no-context)
	(princ "no context (current) module is set!")))
    ;;
    (with-in-module (*current-module*)
      (prepare-for-parsing *current-module*)
      (let ((*parse-variables* nil))
	(let ((res (simple-parse *current-module* value *cosmos*)))
	  (setq res (car (canonicalize-variables (list res) *current-module*)))
	  ;; we treate $$term & $$subterm, we must copy for
	  ;; avoiding side effect.
	  (when (or (equal "$$term" sym) (equal "$$subtem" sym))
	    (setq res (simple-copy-term res)))
	  (when (set-bound-value sym res)
	    (when (and (at-top-level) (not *chaos-quiet*))
	      (format t "~&-- setting let variable \"~a\" to :" sym)
	      (let ((*fancy-print* nil)
		    (*print-indent* (+ *print-indent* 4)))
		(print-next)
		(term-print res) 
		(print-check 0 3)
		(princ " : ")
		(print-sort-name (term-sort res)))))
	  t)))))

;;;=============================================================================
;;; MACRO
;;;=============================================================================

(defun eval-macro (ast)
  (let ((pre-lhs (%macro-lhs ast))
	(pre-rhs (%macro-rhs ast))
	lhs
	rhs
	macro)
    (I-miss-current-module eval-macro)
    (prepare-for-parsing *current-module*)
    (let ((*parse-variables* nil)
	  (*macroexpand* nil))
      (setq lhs (simple-parse *current-module* pre-lhs *cosmos*))
      (when (term-ill-defined lhs)
	(with-output-chaos-error ('invalid-macro-lhs)
	  (format t "no parse for LHS of the macro declaration: ")
	  (print-chaos-object ast)))
      (setq rhs (simple-parse *current-module* pre-rhs *cosmos*))
      (when (term-ill-defined rhs)
	(with-output-chaos-error ('invalid-macro-rhs)
	  (format t "no parse for RHS of the macro declaration: ")
	  (print-chaos-object ast)))
      (unless (term-is-application-form? lhs)
	(with-output-chaos-error ('invalid-macro)
	  (format t "macro can only be defined for normal application form.~%")
	  (print-chaos-object ast)))
      (unless (theory-info-empty-for-matching
	       (method-theory-info-for-matching
		(term-head lhs)))
	(with-output-chaos-error ('invalid-macro)
	  (format t "macro can only be defined for operators with no equational theory.~%")
	  (print-chaos-object ast)))
      ;; LHS & RHS must be of the same sort -- too rigid?
      (unless (is-in-same-connected-component (term-sort lhs)
					      (term-sort rhs)
					      *current-sort-order*)
	(with-output-chaos-error ('invalid-macro)
	  (format t "sort of LHS & RHS of the maro declaration must be the same.")
	  (terpri)
	  (print-chaos-object ast)))
      ;;
      ;; check in 
      (let ((canon (canonicalize-variables (list lhs rhs) *current-module*)))
	(setq macro (make-macro :lhs (first canon) :rhs (second canon)))
	(add-macro-to-module *current-module* macro))
      ;; set module status
      (set-needs-parse)
      macro)))

;;;=============================================================================
;;; 				     MODULE
;;;=============================================================================

;;; DECLARE-MODULE : module-declaration-form -> module
;;;
(defun declare-module (decl)
  ;; need not *current-module*
  (let ((mod nil)			; will bound created module.
	(name (%module-decl-name decl))
	(kind (%module-decl-kind decl))
	(type (%module-decl-type decl))
	(body (%module-decl-elements decl))
	(*allow-$$term* nil)
	(*modexp-eval-table* nil)
	(auto-context? *auto-context-change*)
	(*auto-context-change* nil))
    (declare (special *modexp-eval-table*
		      *auto-context-change*))
    (unless *chaos-quiet*
      (if (equal name "%")
	  (with-output-msg ()
	    (princ "opening module ")
	    (print-mod-name *open-module*)
	    (force-output))
	  (unless (modexp-is-parameter-theory name)
	      (format t "~&-- defining ~(~a~) ~a" (case kind
						    (:object "module!")
						    (:theory "module*")
						    (otherwise "module"))
		      name)
	      (force-output))))
    ;;
    (let ((modval (eval-modexp name nil nil))
	  (recover-same-context nil))
      (unless (or (modexp-is-error modval)
		  (and (module-p modval)
		       (modexp-is-parameter-theory (module-name modval)))
		  (equal "%" name)
		  (eq '% name)
		  (equal " % % " name))

	  (unless (modexp-is-parameter-theory name)
	    (when (module-is-hard-wired modval)
	      (with-output-chaos-error ('invalid-module-decl)
		(format t "You can not redefine system module ~a ." name)))
	    (when (module-is-write-protected modval)
	      (with-output-chaos-error ('invalid-module-decl)
		(format t "Module ~a is protected!" name)))
	    (with-output-chaos-warning ()
	      (format t "Redefining module ~a " name)))
	;;
	(propagate-module-change modval)
	;;
	(when (eq modval *last-module*)
	  (setq *last-module* nil)
	  (setq recover-same-context t))
	
	(when (eq modval *memoized-module*)
	  (clear-term-memo-table *term-memo-table*))
	(when (eq modval .memb-last-module.)
	  (clear-memb-hash))
	;;
	(setq name (module-name modval))
	(clear-module-instance-db modval)
	(when (eq $$term-context modval)
	  (setq $$term nil
		$$term-context nil
		$$subterm nil
		$$action-stack nil
		$$selection-stack nil))
	)

      ;; process declaration forms.
      (setf mod (create-module name))
      (setf (module-kind mod) kind)
      (setf (module-type mod) type)
      (when *save-definition* (setf (module-decl-form mod) decl))
      (let ((*top-level-definition-in-progress*
	     (or *top-level-definition-in-progress*
		 mod)))
	;; construction process is done in the context of `mod'.
	(with-in-module (mod)
	  (add-modexp-defn name mod)
	  ;; operate on mod by side-effect ----------------
	  ;; EVAL EACH MODULE CONSTRUCTS.
	  (dolist (e body)
	    (flet ((report-decl-error (&rest ignore)
		     (declare (ignore ignore))
		     (unless *chaos-quiet*
		       (with-output-msg ()
			 (format t "failed to evaluate the form:~%")
			 (print-ast e)
			 (force-output)))
		     (chaos-error 'declaration-failed)))
	      ;;
	      (with-chaos-error (#'report-decl-error)
		(eval-ast e))
	      (print-in-progress "."))))
	;; FINAL SET UP.
	(let ((real-mod (find-module-in-env name nil)))
	  (final-setup real-mod)
	  (if recover-same-context
	      (setq *last-module* real-mod)
	      (if auto-context?
		  (change-context *last-module* real-mod)))
	  ;;
	  (unless (module-is-parameter-theory real-mod)
	    (print-in-progress " done."))
	  ;;
	  real-mod)))))

;;;=============================================================================
;;; 				      VIEW
;;;=============================================================================

;;; DECLARE-VIEW : definition -> View
;;;
(defun declare-view (decl)
  (let ((name (%view-decl-name decl))
	(view (%view-decl-view decl))
	(*auto-context-change* nil)
	(*current-module* nil))
    (declare (special *auto-context-change*))
    (let ((real-name (normalize-modexp name))
	  new-view)
      (let ((vw (find-view-in-env real-name)))
	(unless *chaos-quiet*
	  (format *error-output* "~&-- defining view ~a " name))
	(when vw
	  (with-output-chaos-warning ()
	    (format t "redefining view ~a " real-name))
	  (propagate-view-change vw)
	  )
	;; 
	(setq new-view (complete-view view))
	(setf (view-name new-view) real-name)
	(setf (view-decl-form new-view) view)
	(if vw
	    (copy-view new-view vw)
	    (setq vw new-view))
	;;
	(add-depend-relation vw :view (view-src vw))
	(add-depend-relation vw :view (view-target vw))
	(add-view-defn real-name vw)
	(print-in-progress " done.")
	;;
	(mark-view-as-consistent vw)
	vw))))

;;;=============================================================================
;;;				  IMPORTATION
;;;=============================================================================

;;; EVAL-IMPORT-MODEXP : import-decl -> {cur_mod} 
;;;-----------------------------------------------------------------------------

(defun eval-import-modexp (decl)
  (I-miss-current-module eval-import-modexp)
  (let ((mode (%import-mode decl))
	(modexp (%import-module decl))
	(parameter (%import-parameter decl))
	(alias (%import-alias decl))
	(new-mod nil))
    (when (and (%is-modexp modexp)
	       (equal (%modexp-value modexp) "THE-LAST-MODULE"))
      (setf (%modexp-value modexp) *last-module*))
    (setf new-mod (import-module *current-module* mode modexp parameter alias))
    new-mod))

;;; !ADD-US
;;;-----------------------------------------------------------------------------
;;; NOT YET

#||
(defun !add-us (e)
  ;; expansion top-level-eval
  (let ((mepars (parse-modexp (third e))))
  (if (and (consp mepars) (eq 'with (car mepars)))
      (!add-using-with *current-module* mepars)
      (let ((val (eval-modexp mepars nil nil)))
	(if (eq *TRUTH-module* val) 
	    (with-output-chaos-warning ()
	      (princ "using TRUTH not allowed, replaced by extending")
	      (print-next)
	      (princ "in module ") (print-mod-name *current-module*)
	      (import-module *current-module* :extending val))
	    (if (eq *current-module* val)
		(with-output-chaos-warning ()
		  (princ "module cannot use itself (ignored)."))
		(import-module *current-module* :using val))))
      )))
||#

#||
;;; handle using X with A and B
(defun !add-using-with (module mepars)
  (let ((mod (eval-modexp (cadr mepars))))
    (when (modexp-is-error mod)
      (with-output-chaos-error ()
	(princ "cannot evaluate module: ")
	(print-modexp (cadr mepars))
	(chaos-to-top)))
    (let ((submods (let ((*current-module* mod))
		     (mapcar #'(lambda (me)
				 (let ((val (eval-modexp me)))
				   (when (modexp-is-error val)
				     (with-output-chaos-error ()
				       (princ "cannot evaluate module: ")
				       (print-modexp me)
				       (terpri)
				       (chaos-to-top)))
				   val))
			     (if (equal '(nil) (caddr mepars))
				 nil
				 (caddr mepars))))))
      (incorporate-using-with module mod submods))))

;;; Labels in Axioms env.
;;;-----------------------------------------------------------------------------
;;; PROCESS-LABELS : LIST[Token] -> LIST[Token]
;;; might instead want to group sequences of tokens between ","s together
;;
(defun process-labels (x)
  (let ((val (delete "," x :test #'equal)) (res nil))
    (dolist (l val)
      (if (find #\. l)
	  (with-output-chaos-warning ()
	    (princ "label ")
	    (princ l)
	    (princ " contains a '.' (ignored)") (terpri))
	  (if (digit-char-p (char l 0))
	      (with-output-chaos-warning ()
		(princ "label ")
		(princ l)
		(princ " contains an initial digit (ignored)") (terpri))
	      (push l res)))
      )
    (nreverse res)
    ))


;;;=============================================================================
;;; MISC.

;;; AS
;;;-----------------------------------------------------------------------------
;;; !ADD-AS
;;;
(defun !add-as (e)
  (unless (module-is-prepare-for-parsing *current-module*)
    (prepare-for-parsing *current-module*))
  (with-in-module (*current-module*)
    (let* ((so (module-sort-order *current-module*))
	   (sort (find-sort-in *current-module* (nth 1 e)))
	   (tm (parser$parses *current-module* (nth 3 e)
			      (if sort sort *cosmos*)))
	   (cnd (parser$parses *current-module* (nth 5 e))))
      (when (null sort)
	(princ "Unknown sort in sort constraint"))
      (when (null tm)
	(princ "No parse for term in sort constraint") (terpri))
      (when (or (null cnd) (not (null (cdr cnd))))
	(princ "No single parse for condition in sort constraint") (terpri))
      (if (and tm (not (null (cdr tm))))
	  (when tm (princ "Term in sort constraint is ambiguous") (terpri))
	  (when (and tm (null (cdr tm)))
	    (when (and sort tm)
	      (unless (sort-order$is-included-in so sort (term$sort (car tm)))
		(princ "Specified sort and sort of term incompatible")))
	    (when (and tm cnd (null (cdr tm)) (null (cdr cnd)))
	      (unless (subsetp (term$vars (car cnd)) (term$vars (car tm)))
		(princ "Condition variables not subset of those in term") (terpri)))
	    )))
    (error "** Error: general sort constraint not currently handled (ignored)")
    (terpri)
    (princ "    ")
    (princ "as ")
    (simple-princ-open (nth 1 e))
    (princ " : ")
    (simple-princ-open (nth 3 e))
    (princ " if ")
    (simple-princ-open (nth 5 e))
    (princ " .")
    (terpri)
    ))

;;; OP-AS
(defun !add-op-as (e)
  ;(!add-sort-constraint
  ; (nth 7 e) (nth 5 e) (nth 9 e))
  (with-output-chaos-warning ()
    (princ "operator assertion being treated simply as a")
    (princ " declaration") (print-next)
    (princ "for operator: ") (print-simple-princ-open (nth 1 e)) (terpri))
  (!add-op
   `("op" ,(nth 1 e) ":" ,(nth 3 e) "->" ,(nth 5 e)
	  ,@(if (equal "." (nth 10 e)) nil  (list (nth 10 e)))
	  "."))
  )

||#

;;; EOF
