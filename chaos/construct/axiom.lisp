;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: axiom.lisp,v 1.10 2010-07-15 04:40:55 sawada Exp $
(in-package :chaos)
#|=============================================================================
				  System:CHAOS
				Module:construct
				File:axiom.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; (defvar *on-axiom-debug* nil)

;;; ****************
;;; RULE CONSTRUCTOR
;;; ****************
(defun make-rule (&key lhs rhs condition type id-condition behavioural
		       extensions
		       kind first-match-method
		       next-match-method 
		       labels
		       (meta-and-or nil)
		       no-method-computation)
  (declare (type (or null term) lhs rhs)
	   (type list condition)
	   (type symbol type)
	   (type t id-condition extensions kind first-match-method
		 next-match-method labels)
	   (type (or null t) behavioural no-method-computation)
	   (values axiom))
  ;; *NOTE* now rewrite rule is just same to AXIOM, there are some
  ;;        room for optimization.
  (let ((rule (create-axiom lhs
			    rhs
			    condition
			    type
			    behavioural
			    id-condition
			    extensions
			    kind
			    first-match-method
			    next-match-method
			    labels
			    meta-and-or)))
    (if (term-is-lisp-form? rhs)
	(setf (axiom-rhs rule)
	  (convert-lisp-form-term rhs (axiom-lhs rule)))
      (if (and (term-is-builtin-constant? rhs)
	       (sort= (term-sort rhs) *chaos-value-sort*))
	  (convert-chaos-expr rhs (axiom-lhs rule))))
    (unless no-method-computation
      (compute-rule-method rule))
    rule))

(defun make-simple-axiom (lhs rhs type &optional behavioural meta-and-or)
  (declare (type term lhs rhs)
	   (type (or null t) behavioural))
  (make-rule :lhs lhs
	     :rhs rhs
	     :condition *bool-true*
	     :behavioural behavioural
	     :id-condition nil
	     :type type
	     :kind nil
	     :labels nil
	     :meta-and-or meta-and-or))
;;;
(defun make-fun (f)
  #+GCL f
  #+EXCL
  (if *compile-builtin-axiom*
      (compile nil f)
    f)
  #+:CCL
  (eval `(function ,f))
  #+(or CLISP CMU SBCL)
  (if *compile-builtin-axiom*
      (compile nil f)
    (eval `(function ,f)))
  )

(defun make-fun* (f)
  #+(or CMU EXCL GCL CLISP SBCL)
  (if *compile-builtin-axiom*
      (compile nil f)
    #+(or CMU CLISP SBCL)
    (eval `(function ,f))
    #-(or CMU CLISP SBCL)
    f)
  #+:CCL
  (eval `(function ,f))
  )

(declaim (type fixnum xsim-counter))
(defvar xsim-counter 0)

(defun convert-lisp-form-term (term lhs)
  (declare (type term term lhs))
  (let* ((variables (term-variables lhs))
	 (form (lisp-form-original-form term))
	 (parameters (mapcar #'(lambda (v)
				(intern (string-upcase (string (variable-name
								v))))) 
			     variables))
	 (fun-body nil)
	 (new-term nil))
    (cond ((term-is-simple-lisp-form? term)
	   (let ((s-simbol (intern (format nil "slisp-sort-~D"
					   (incf xsim-counter)))))
	     (setf (get s-simbol :sort) (term-sort lhs))
	     (setf fun-body
		   (make-fun*
		    ` (lambda (subst)
			(invoke-simple-lisp-fun
			 ',(make-fun `(lambda ,parameters ,form))
			 ',(reverse (mapcar #'(lambda (x)
						(variable-name x))
					    variables))
			 subst
			 ',s-simbol))
		      )
		   )))
	  ((term-is-general-lisp-form? term)
	   (setf fun-body
		 (make-fun* `(lambda (subst)
                              (invoke-general-lisp-fun
                               ',(make-fun `(lambda ,parameters ,form))
                               ',(reverse (mapcar #'(lambda (x)
						      (variable-name x))
						  variables))
                               subst)))))
	  (t (error "Internal error: invalid lisp form term ~s" term)))
    (setf new-term (if (term-is-simple-lisp-form? term)
		       (make-simple-lisp-form-term (lisp-form-original-form
						    term)) 
		       (make-general-lisp-form-term (lisp-form-original-form
						     term)))) 
    (setf (lisp-form-function new-term) fun-body)
    (setf (term-sort new-term) (term-sort lhs))
    new-term))

(defun convert-chaos-expr (term lhs)
  (declare (type term term lhs))
  (let* ((variables (term-variables lhs))
	 (form (list 'eval-ast2 (term-builtin-value term)))
	 (parameters (mapcar #'(lambda (v)
				(intern (string-upcase (string (variable-name
								v))))) 
			     variables))
	 (fun-body nil))
    ;;
    (setf fun-body
      (make-fun*
       ` (lambda (subst)
	   (eval-chaos-expr
	    ',(make-fun `(lambda ,parameters ,form))
	    ',(reverse (mapcar #'(lambda (x)
				   (variable-name x))
			       variables))
	    subst))
	 )
      )
    (setf (term-builtin-value term)
      (list '|%Chaos| fun-body (term-builtin-value term)))
    term))

;;; ************************
;;; BUILT-IN RULE EVALUATORS
;;; ************************

(defun invoke-general-lisp-fun (fun vars substitution)
  (declare (type list vars substitution))
  (macrolet ((subst-image-by-name (v-name)
	       ` (dolist (b substitution '((error image)))
		   (when (equal ,v-name (variable-name (car b)))
		     (return (cdr b))))))
    (let ((bindings nil))
      (dolist (v vars)
	(push (subst-image-by-name v) bindings))
      (catch 'rewrite-failure
	(values (apply fun bindings) t)))))

(defun is-metalevel-special-sort (sort)
  (gethash sort *builtin-metalevel-sort*))

(defun invoke-simple-lisp-fun (fun vars substitution sort-x)
  (declare (type function fun)
	   (type list vars substitution)
	   (type t sort-x)
	   (values t t))
  (macrolet ((subst-image-by-name (v-name)
	       ` (dolist (b substitution nil)
		   (when (equal ,v-name (variable-name (car b)))
		     (return (cdr b)))))
	     (coerce-lisp-to-term (sort value)
	       ` (if (sort= *bool-sort* ,sort)
		     (if ,value
			 *bool-true*
		       *bool-false*)
		   (if (is-metalevel-special-sort sort)
		       ,value
  		     (make-bconst-term ,sort ,value)))))
    ;;
    (block invoke
      (let ((bindings nil)
	    (sort (get sort-x :sort)))
	(dolist (v vars)
	  (let ((value (subst-image-by-name v)))
	    (if value
		(if (term-is-pure-builtin-constant? value)
		    (push (term-builtin-value value) bindings)
		    (if *reduce-builtin-eager*
			(let ((args (term-subterms value)))
			  (dolist (a args) (normalize-term a))
			  (if (every #'(lambda (x)
					 (and (term-is-builtin-constant? x)
					      (not (term-is-psuedo-constant? x))))
				     args)
			      (progn
				(normalize-term value)
				(if (term-is-builtin-constant? value)
				    (push (term-builtin-value value) bindings)
				    (return-from invoke (values nil nil))))
			      (return-from invoke (values value t))))
			(return-from invoke (values nil nil)))
		    )
		(return-from invoke (values nil nil))
		)))
	(if (sort-is-builtin sort)
 	    (values (make-bconst-term sort
				      (apply fun bindings))
		    t)
	    (values (coerce-lisp-to-term sort (apply fun bindings))
		    t))))))

(defun eval-chaos-expr (fun vars substitution)
  (declare (type function fun)
	   (type list vars substitution)
	   (values t t))
  (macrolet ((subst-image-by-name (v-name)
	       ` (dolist (b substitution nil)
		   (when (equal ,v-name (variable-name (car b)))
		     (return (cdr b))))))
    ;;
    (block invoke
      (let ((bindings nil)
	    (sort *chaos-value-sort*))
	(dolist (v vars)
	  (let ((value (subst-image-by-name v)))
	    (if value
		(if (term-is-pure-builtin-constant? value)
		    (push (term-builtin-value value) bindings)
		    (if *reduce-builtin-eager*
			(let ((args (term-subterms value)))
			  (dolist (a args) (normalize-term a))
			  (if (every #'(lambda (x)
					 (and (term-is-builtin-constant? x)
					      (not (term-is-psuedo-constant? x))))
				     args)
			      (progn
				(normalize-term value)
				(if (term-is-builtin-constant? value)
				    (push (term-builtin-value value) bindings)
				    (return-from invoke (values nil nil))))
			      (return-from invoke (values value t))))
			(return-from invoke (values nil nil)))
		    )
		(return-from invoke (values nil nil))
		)))
	(values (make-bconst-term sort
				  (apply fun bindings))
		t)
	))))

;;;
;;;
;;;
(defun make-ext-rule-label (ls modif)
  (let ((lbl (car ls)))
    (if lbl
	(list (intern (format nil "~a_ext_~a" lbl modif)))
      nil)))


;;; COMPUTE-A-EXTENSIONS : rule method -> List[Rule]
;;;-----------------------------------------------------------------------------
;;; Compute the list of associative extensions
;;;
(defun compute-A-extensions (rule top)
  (declare (type axiom rule)
	   (type method top)
	   (values list))
  (let ((knd (axiom-kind rule)))
    (when *on-axiom-debug*
      (format t "~%[A-extension] ")
      (print-chaos-object rule)
      (format t "~%  kind=~S" knd))
    (if (and knd (or (eq :id-theorem knd) (eq :idem-theory knd)))
	(setf  (!axiom-A-extensions rule) '(nil nil nil))
      (let ((listext nil)
	    ext-rule
	    (new-var (make-variable-term *cosmos* 'A1))
	    (new-var2 (make-variable-term *cosmos* 'A2)))

	;; first the left associative extension
	(setf ext-rule
	  (make-rule
	   :lhs (make-right-assoc-normal-form top
					      (cons new-var
						    (list-assoc-subterms
						     (axiom-lhs rule)
						     (term-method
						      (axiom-lhs rule)))))
	   :rhs (make-applform (method-coarity top)
			       top
			       (list new-var
				     ;;(substitution-check-builtin
				     ;; (axiom-rhs rule))
				     (axiom-rhs rule)
				     ))
	   :condition (axiom-condition rule)
	   :id-condition (axiom-id-condition rule)
	   :type (axiom-type rule)
	   :labels (make-ext-rule-label (axiom-labels rule) "A-l")
	   :behavioural (axiom-is-behavioural rule)
	   :kind (if (eq :id-theorem knd)
		     :id-ext-theory
		   :A-left-theory)
	   :meta-and-or (axiom-meta-and-or rule)))
	;; (compute-rule-method ext-rule)
	(push ext-rule listext)

	;; the right associative extension:
	(setf ext-rule
	  (make-rule
	   :lhs (make-right-assoc-normal-form top
					      (append
					       (list-assoc-subterms
						(axiom-lhs rule)
						(term-method
						 (axiom-lhs rule)))
					       (list new-var)))
	   :rhs (make-applform (method-coarity top)
			       top
			       (list (axiom-rhs rule)
				     new-var))
	   :condition (axiom-condition rule)
	   :id-condition (axiom-id-condition rule)
	   :type (axiom-type rule)
	   :behavioural (axiom-is-behavioural rule)
	   :labels (make-ext-rule-label (axiom-labels rule) "A-r")
	   :kind (if (eq :id-theorem knd)
		     :id-ext-theory
		   :A-right-theory)
	   :meta-and-or (axiom-meta-and-or rule)))
	;; (compute-rule-method ext-rule)
	(push ext-rule listext)

	;; the middle associative extension:
	(setf ext-rule
	  (make-rule
	   :lhs (make-right-assoc-normal-form top
					      (list new-var2
						    (axiom-lhs rule)
						    new-var))
	   :rhs (make-right-assoc-normal-form top
					      (list new-var2
						    (axiom-rhs rule)
						    new-var))
	   :condition (axiom-condition rule)
	   :id-condition (axiom-id-condition rule)
	   :type (axiom-type rule)
	   :behavioural (axiom-is-behavioural rule)
	   :labels (make-ext-rule-label (axiom-labels rule) "A-m")
	   :kind (if (eq :id-theorem knd)
		     :id-ext-theory
		   :A-middle-theory)
	   :meta-and-or (axiom-meta-and-or rule)))
	;;
	(push ext-rule listext)
	(setf (axiom-A-extensions rule) listext))
      )))


;;; COMPUTE-AC-EXTENSION : rule method -> List[Rule]
;;;-----------------------------------------------------------------------------
;;; Compute the list of associative commutative extensions.
;;;
(defun compute-AC-extension (rule top)
  (declare (type axiom rule)
	   (type method top)
	   (values list))
  ;;(declare (optimize (speed 3) (safety 0)))
  (let ((knd (axiom-kind rule)))
    (if (and knd (not (eq :id-theorem knd)) (not (eq :idem-theory knd)))
	(setf (!axiom-AC-extension rule)
	  ;; '(nil)
	  nil)
      (let (ext-rule
	    (new-var (make-variable-term (car (method-arity top))
					 ;; *cosmos*
					 'AC)))
	(setf ext-rule
	  (make-rule
	   :lhs (make-right-assoc-normal-form top
					      (cons new-var
						    (list-assoc-subterms
						     (axiom-lhs rule)
						     (term-method
						      (axiom-lhs rule)))))
	   :rhs (make-applform (method-coarity top)
			       top
			       (list new-var
				     (axiom-rhs rule)
				     ))
	   :condition (axiom-condition rule)
	   :type (axiom-type rule)
	   :behavioural (axiom-is-behavioural rule)
	   :id-condition (axiom-id-condition rule)
	   :labels (make-ext-rule-label (axiom-labels rule) "AC")
	   :kind (if (eq ':id-theorem knd)
		     ':id-ext-theory
		   ':ac-theory)
	   :meta-and-or (axiom-meta-and-or rule)))
	  ;;
	(setf (axiom-AC-extension rule) (list ext-rule))
	))))


;;; GIVE-AC-EXTENSION : rule -> List[Rule]
;;;-----------------------------------------------------------------------------
;;; compute the list of AC extension of the 'rule'
;;;
(defun give-AC-extension (rule)
  (declare (type axiom rule)
	   (values list))
  (let ((listext (!axiom-AC-extension rule)))
    (when (or (null listext) (null (car listext)))
      ;; then need to pre-compute the extensions and store then
      (setq listext (compute-AC-extension 
		     rule (term-method (axiom-lhs rule)))))
    listext))

;;; GIVE-A-EXTENSIONS : rule -> List[Rule]
;;;-----------------------------------------------------------------------------
;;; compute the list of A extensions of the 'rule'.
;;;
(defun give-A-extensions (rule)
  (declare (type axiom rule)
	   (values list))
  (let ((listext (!axiom-A-extensions rule)))
    (when (or (null listext) (null (car listext)))
      ;; then need to pre-compute the extensions and store then
      (setq listext (compute-A-extensions
		     rule (term-method (axiom-lhs rule)))))
    listext))

;;; COMPUTE-RULE-METHOD : rule -> rule'
;;;-----------------------------------------------------------------------------
;;; set appropriate rewrite method for rule.
;;;
(defun compute-rule-method (rule)
  (declare (type axiom rule)
	   (values t))
  (let ((m (choose-match-method (axiom-lhs rule)
				(axiom-condition rule)
				(axiom-kind rule))))
    (setf (axiom-first-match-method rule) (car m))
    (setf (axiom-next-match-method rule) (cdr m))
    rule))
	 
;;; RULE-COPY : rule -> rule
;;;-----------------------------------------------------------------------------
;;; Returns a copy of "rule". The variable occuring in the rule are also
;;; copied and are shared by the right and left hand side. 
;;; U: used by "rule-gen$$specialize-on-sorts".
;;; *ck12may87*: Modified by adding A and AC extensions fields. In the copy 
;;; there are supposed to be empty.
;;;
(defvar copy-conditions nil)

(defun rule-copy (rule)
  (declare (type axiom rule)
	   (values axiom))
  (let ((new-rule nil))
    (multiple-value-bind (new-lhs list-new-var)
	(term-copy-and-returns-list-variables (axiom-lhs rule))
      (setq new-rule (make-rule
		      :lhs new-lhs
		      :condition (if (is-true? (axiom-condition rule))
				     *bool-true*
				   (copy-term-using-variable (axiom-condition rule)
							     list-new-var))
		      :id-condition (if (null (axiom-id-condition rule))
					nil
				      (if (is-true? (axiom-id-condition rule))
					  *bool-true*
					(term-copy-id-cond
					 (axiom-id-condition rule) list-new-var)))
		      :rhs (copy-term-using-variable (axiom-rhs rule)
						     list-new-var)
		      :type (axiom-type rule)
		      :behavioural (axiom-is-behavioural rule)
		      ;; :end-reduction (copy-list (axiom-end-reduction rule))
		      :first-match-method (axiom-first-match-method rule)
		      :next-match-method (axiom-next-match-method rule)
		      :labels (copy-list (axiom-labels rule))
		      :kind (axiom-kind rule)
		      :meta-and-or (axiom-meta-and-or rule)))
      (compute-rule-method new-rule)
      new-rule)))

(defun term-copy-id-cond (tm vars)
  (declare (type (or null term) tm)
	   (type list vars))
  (cond
   ((null tm) nil)
   ((term-is-variable? tm)
    (let ((val (assoc tm vars)))
      (if val
	  (cdr val)
	(variable-copy tm)		; This should never occur
	)))
   (t (make-applform (method-coarity (term-method tm))
		     (term-method tm)
		     (mapcar #'(lambda (stm)
				 (term-copy-id-cond stm vars))
			     (term-subterms tm))))))


;;; ******************
;;; REWRITE RULE UTILS
;;; ******************

;;; RULE-IS-SIMILAR? rule rule : -> Bool
;;;-----------------------------------------------------------------------------
;;; returns true iff the rules are similar, i.e.  lhs, rhs, and condition are
;;; congruent.  
;;; 
(defun term-is-congruent-2? (t1 t2)
  (declare (type term t1 t2)
	   (values (or null t)))
  (let ((t1-body (term-body t1))
	(t2-body (term-body t2)))
    (cond ((term$is-variable? t1-body)
	   (or (eq t1 t2)
	       (and (term$is-variable? t2-body)
		    #||
		    ;; (eq (variable$name t1-body) (variable$name t2-body))
		    (sort= (variable$sort t1-body) (variable$sort t2-body))
		    ||#
		    (variable= t1 t2)
		    )))
	  ((term$is-variable? t2-body) nil)
	  ((term$is-application-form? t1-body)
	   (and (term$is-application-form? t2-body)
		(if ;;(method-is-same-qual-method (term$method t1-body)
		    ;;				(term$method t2-body))
		    (method-is-of-same-operator+ (term$method t1-body)
						 (term$method t2-body))
		    (let ((sl1 (term$subterms t1-body))
			  (sl2 (term$subterms t2-body)))
		      (loop (when (null sl1) (return (null sl2)))
			    (unless (term-is-congruent-2? (car sl1) (car sl2))
			      (return nil))
			    (setf sl1 (cdr sl1)
				  sl2 (cdr sl2))))
		    nil)))
	  ((term$is-builtin-constant? t1-body)
 	   (term$builtin-equal t1-body t2-body))
	  ((term$is-builtin-constant? t2-body) nil)
	  ((term$is-lisp-form? t1-body)
	   (and (term$is-lisp-form? t2-body)
		(equal (term$lisp-function t1-body)
		       (term$lisp-function t2-body))))
	  ((term$is-lisp-form? t2-body) nil)
	  (t (break "Panic! unknown type of term to term-is-congruent?")))))

(defun rule-is-similar? (r1 r2)
  (declare (type axiom r1 r2)
	   (values (or null t)))
  (and (term-is-congruent-2? (axiom-lhs r1) (axiom-lhs r2))
       (term-is-congruent-2? (axiom-condition r1) (axiom-condition r2))
       (term-is-congruent-2? (axiom-rhs r1) (axiom-rhs r2))))

;;; RULE-MEMBER : Rule RuleSet -> Bool
;;;-----------------------------------------------------------------------------
;;; returns true iff the 'rule' is in 'ruleset', equality used is
;;; rule-is-similar?. 
;;;
(defun rule-member (r l)
  (declare (type axiom r)
	   (type list l)
	   (values (or null t)))
  (dolist (e l nil)
    (when (rule-is-similar? r e) (return t))))

;;; ADJOIN-RULE : rule ruleset -> ruleset
;;;-----------------------------------------------------------------------------
;;; adjoin rule to rule set. 
;;; when the rule is added it is added to a returned value.
;;;
(defparameter .ext-rule-kinds.
    '(:id-theorem :idem-theory :id-ext-theory :ac-theory :A-middle-theory
      :A-right-theory :A-left-theory))

(defun adjoin-rule (rule rs)
  (declare (type axiom rule)
	   (type list rs)
	   (values list))
  (do* ((lst rs (cdr lst))
	(r (car lst) (car lst)))
       ((null lst) (cons rule rs))
    (when (rule-is-similar? rule r)
      (when (and *chaos-verbose*
		 (not (eq rule r))
		 (not (member (axiom-kind rule) .ext-rule-kinds.))
		 )
	(with-output-msg ()
	  (format t "a similar pair of axioms is found:")
	  (print-next)
	  (format t  "(1:~x)" (addr-of rule))
	  (print-axiom-brief rule)
	  (print-next)
	  (format t "(2:~x)" (addr-of r))
	  (print-axiom-brief r)))
      (let ((newlhs (axiom-lhs rule))
	    (oldlhs (axiom-lhs r)))
	(when (and (not (term-is-variable? newlhs))
		   (not (term-is-variable? oldlhs))
		   (not (method= (term-method newlhs) (term-method oldlhs)))
		   (sort<= (term-sort oldlhs) (term-sort newlhs)))
	  (rplaca lst rule))
	(return-from adjoin-rule rs)))))

;;; RULE-OCCURS : rule ruleset -> Bool
;;;-----------------------------------------------------------------------------
;;; cf. adjoin-rule
;;;
(defun rule-occurs (rule rs)
  (declare (type axiom rule)
	   (type list rs)
	   (values (or null t)))
  (let ((newlhs (axiom-lhs rule)))
    (do* ((lst rs (cdr lst))
	  (r (car lst) (car lst)))
	 ((null lst) nil)
      (when (and (rule-is-similar? rule r)
		 (let ((oldlhs (axiom-lhs r)))
		   (and (or (term-is-variable? newlhs)
			    (and (not (term-is-variable? oldlhs)) ;very defensive
				 (method= (term-head newlhs) (term-head oldlhs))))
			(sort<= (term-sort oldlhs)
				(term-sort newlhs)))))
	(return t)))))

;;; ***************
;;; RULE-RING UTILS
;;; ***************

;;; RULE-RING-MEMBER rule rule-ring
;;;
(defun rule-ring-member (r rr)
  (declare (type axiom r)
	   (type rule-ring rr)
	   (values (or null t)))
  (do ((rule (initialize-rule-ring rr) (rule-ring-next rr)))
      ((end-of-rule-ring rr) nil)
    (when (rule-is-similar? r rule) (return t))))

;;; RULE-RING-ADJOIN-RULE rule-ring rule
;;; Add a new rule with same top in the rule ring.
;;; Uses `rule-is-similar?' to see if the rule already appeats, if so keep
;;; higher one.  
;;; Return membership indication, t iff the similar rule already exists.
;;;
(defun rule-ring-adjoin-rule (rr rule)
  (declare (type rule-ring rr)
	   (type axiom rule)
	   (values t))
  (do ((r (initialize-rule-ring rr) (rule-ring-next rr)))
      ((end-of-rule-ring rr))
    (when (rule-is-similar? r rule)
      ;; there exists similar rule.
      ;; we don't add, but keeps higher (more general) one.
      (unless *current-module*
	(break "rule-ring-adjoin-rule: need current module")) 
      (let ((newlhs (rule-lhs rule))
	    (oldlhs (rule-lhs r)))
	;; compare lhs of rules.
	(when (and (not (term-is-variable? newlhs))
		   (not (term-is-variable? oldlhs))
		   (not (method= (term-method newlhs) (term-method oldlhs)))
		   (sort<= (term-sort oldlhs) (term-sort newlhs)
			   *current-sort-order*)) 
	  ;; we keep higher one.
	  (rplaca (rule-ring-current rr) rule))
	(return-from rule-ring-adjoin-rule t))))
  ;; No similar rules.
  (add-rule-to-ring rr rule)
  nil)

;;; ***********************
;;; ADDING AXIOMS TO MODULE
;;; ***********************
#||
(defun add-axiom-to-module (module ax)
  (declare (type module module)
	   (type axiom ax)
	   (values t))
  (if (memq (axiom-type ax) '(:equation :pignose-axiom :pignose-goal))
      (push ax (module-equations module))
    (push ax (module-rules module))))
||#

(defun add-axiom-to-module (module ax)
  (adjoin-axiom-to-module module ax)
  )

(defun adjoin-axiom-to-module (module ax)
  (declare (type module module)
	   (type axiom ax)
	   (values t))
  ;; (when (eq (object-context-mod ax) module)
  ;; (let ((labels (axiom-labels ax)))
  ;;   (dolist (lab labels)
  ;; 	(symbol-table-add (module-symbol-table module)
  ;; 			  lab
  ;; 			  ax)))
  ;; )
  (if (memq (axiom-type ax) '(:equation :pignose-axiom :pignose-goal))
      (setf (module-equations module)
	    (adjoin-rule ax (module-equations module)))
      (setf (module-rules module)
	    (adjoin-rule ax (module-rules module)))))

(defun add-rule-to-module (module rule)
  (declare (type module module)
	   (type axiom rule)
	   (values t))
  (add-rule-to-method rule
		      (term-head (axiom-lhs rule))
		      (module-opinfo-table module))
  (pushnew rule (module-rewrite-rules module)
	   :test #'rule-is-similar?)) 

(defun add-rule-to-method (rule method
				&optional (opinfo-table *current-opinfo-table*))
  (declare (type axiom rule)
	   (type method method)
	   (type hash-table opinfo-table))
  ;; set trans-rule flag.
  (when (eq (axiom-type rule) :rule)
    (setf (method-has-trans-rule method opinfo-table) t))
  ;; reset rewrite-strategy
  (setf (method-rewrite-strategy method opinfo-table) nil)
  ;;
  (if (and (term-is-applform? (rule-rhs rule))
	   (method= (rule-lhs rule) (term-method (rule-rhs rule))))
      (rule-ring-adjoin-rule (method-rules-with-same-top method opinfo-table)
			     rule) 
    (setf (method-rules-with-different-top method opinfo-table)
      (adjoin-rule rule (method-rules-with-different-top method
							 opinfo-table)))))

;;; RULE-SUBSUMES : rule rule -> bool
;;;-----------------------------------------------------------------------------
;;; returns true iff the r1 subsumes r2.
;;;
(defun rule-subsumes (r1 r2)
  (declare (type axiom r1 r2)
	   (values (or null t)))
  (or (eq r1 r2)
      (let ((lhs1 (rule-lhs r1))
	    (lhs2 (rule-lhs r2)))
	(or (term-is-variable? lhs1)
	    (and (term-is-application-form? lhs1)
		 (term-is-application-form? lhs2)
		 (method-is-of-same-operator (term-method lhs1)
					     (term-method lhs2))
		 (multiple-value-bind  (gs subst no eeq)
		     (first-match lhs1 lhs2)
		   (declare (ignore gs))
		   (and (or eeq (not no))
			(or (is-true? (rule-condition r1))
			    (let (($$trace-rewrite nil)
				  ($$trace-rewrite-whole nil))
			      (let ((newcond
				     (term-simplify
				      (normalize-for-identity-total
				       (substitution-partial-image
					subst
					(rule-condition r1))))))
				(matches? newcond (rule-condition r2))
				))))))))))

(defun rule-strictly-subsumes (r1 r2)
  (declare (type axiom r1 r2)
	   (values (or null t)))
  (and (rule-subsumes r1 r2)
       (not (rule-subsumes r2 r1))))

;;; ***********************
;;; FINDING SPECIFIED RULES
;;; ***********************

;;; get-rule-numbered : mdoule number -> rule
;;;
(defun get-rule-numbered (mod n)
  (declare (type module mod)
	   (type fixnum n))
  (!setup-reduction mod)
  (when (<= n 0)
    (with-output-chaos-error ()
      (format t "rule number must be greater than 0.")
      (chaos-to-top)))
  (let* ((*module-all-rules-every* t)
	 (res (nth (1- n) (get-module-axioms mod t))))
      (if (null res)
	  (with-output-chaos-error ()
	    (format t "selected rule doesn't exist, ~d" n)
	    (chaos-to-top))
	  res)))

(defun get-all-rules-labelled (mod l)
  (declare (type module mod)
	   (type (or symbol simple-string) l)
	   (values list))
  (!setup-reduction mod)
  (when (stringp l)
    (setq l (intern l)))
  (let ((res nil)
	(*module-all-rules-every* t))
    (dolist (rul (get-module-axioms mod t))
      (when (memq l (axiom-labels rul))
	(push rul res)))
    res))

(defun get-rule-labelled (mod l)
  (declare (type module mod)
	   (type (or symbol simple-string) l))
  (let ((val (get-all-rules-labelled mod l)))
    (if (null val)
	(with-output-chaos-error ()
	  (format t "No rule with label: ~a" l)
	  (chaos-to-top))
	(if (and val (null (cdr val)))
	    (car val)
	    (progn
	      (princ "no unique rule with label: ") (princ l) (terpri)
	      (chaos-to-top)))
	)))

;;; ************************
;;; COMPUTING RULE SPECIFIER
;;; ************************
;;; used by `apply' command & trace/untrace specfic rules.
;;;

(defun make-rule-reverse (rule)
  (declare (type axiom rule))
  (if (rule-is-builtin rule)
      rule
    (make-rule :lhs (axiom-rhs rule)
	       :rhs (axiom-lhs rule)
	       :condition (axiom-condition rule)
	       :labels (axiom-labels rule)
	       :kind (axiom-kind rule)
	       :type (axiom-type rule)
	       ;; :meta-and-or (axiom-meta-and-or rule)
	       ;; :no-method-computation t
	       )))

(defun make-rule-instance (rule subst)
  (declare (type axiom rule)
	   (type list subst)
	   (values axiom))
  (when (and rule (rule-is-builtin rule))
    (with-output-chaos-error ('internal-error)
      (format t "cannot instantiate builtin rules!")))
  (make-rule
   :lhs (substitution-image! subst (axiom-lhs rule))
   :rhs (substitution-image! subst (axiom-rhs rule))
   :condition (let ((cnd (axiom-condition rule)))
		(if (eq *bool-true* cnd)
		    cnd
		    (substitution-image! subst cnd)))
   :labels (axiom-labels rule)
   :type (axiom-type rule)
   :kind (axiom-kind rule)
   :meta-and-or (axiom-meta-and-or rule)))

;;; compute-action-rule : rule-spec subst-list -> rule
;;;  rule-spec ::= ( <ModId> { <Nat> | <Id> } <Reverse> )
;;; get a rule to be used for applying, reverses the direction if
;;; specified in rule-spec, and also applies variable substitution specified.
;;;
(defun compute-action-rule (rule-spec subst-list &optional selectors)
  (declare (ignore selectors)
	   (type list rule-spec subst-list selectors)
	   (values axiom module))
  (let ((mod (first rule-spec))
	(rule-id (second rule-spec))
	(rule nil))			; the result
    (declare (type (or module modexp) mod)
	     (type simple-string rule-id))
    ;; we always need rule specifier
    (when (equal "" rule-id)
      (with-output-chaos-error ('invalid-rule-spec)
	(format t "No rule number or name is specified.")
	))
    ;; get module in which the specified rule is looked up
    (if (equal "" mod)
	(setq mod *last-module*)
      (if (and *last-module*
	       (equal "%" (module-name *last-module*))
	       (module-submodules *last-module*)
	       (equal mod
		      (module-name
		       (caar (module-submodules *last-module*)))))
	  (setq mod *last-module*)
	;; we also find in local modules
	(setq mod (eval-modexp mod t))))
    ;;
    (unless mod
      (with-output-chaos-error ('no-context)
	(princ "no context module.")))
    ;;
    (when (modexp-is-error mod)
      (let ((nxt (eval-mod (list (car rule-spec)))))
	(if (modexp-is-error nxt)
	    (with-output-chaos-error ('invalid-module)
	      (format t "module is undefined or unreachable: ~a" (car rule-spec))
	      )
	    (setq mod nxt))))
    ;; check context
    (unless (eq *last-module* mod)
      (let ((e-mod (assoc mod (module-all-submodules *last-module*))))
	(unless e-mod
	  (with-output-chaos-error ('invalid-context)
	    (format t "specified module is out of current context: ")
	    (print-simple-mod-name mod)))
	(unless (member (cdr e-mod)
			'(:protecting :extending :using))
	  (with-output-chaos-error ('invalid-rule-ref)
	    (format t "you cannot refer the rule ~a of module " rule-spec)
	    (print-simple-mod-name mod)
	    (princ " directly.")))))
    ;;
    (with-in-module (mod)
      ;; find specified rule
      (if (and (< 0 (length rule-id))
	       (every #'digit-char-p rule-id))
	  (setq rule (get-rule-numbered mod (str-to-int rule-id)))
	  (setq rule (get-rule-labelled mod rule-id)))
      ;; make rule reverse order if need
      (when (nth 2 rule-spec) (setq rule (make-rule-reverse rule)))
      ;; apply variable substitution 
      (when subst-list
	(setq rule
	      (make-rule-instance rule (compute-variable-substitution
					rule subst-list))))
      )
    ;; the result
    (when *on-axiom-debug*
      (with-output-simple-msg ()
	(princ "[compute-action-rule]: rule= ")
	(print-chaos-object rule)))
    ;;
    (values rule mod)
    ))


;;; CHECK-AXIOM-ERROR-METHOD : Module Axiom -> Axiom
;;;

(defvar *optimize-error-operators* t)

(defun check-axiom-error-method (module axiom &optional message?)
  (declare (type module module)
	   (type axiom axiom)
	   (type (or null t) message?)
	   (values axiom))
  (let ((new-axiom (cdr (assq axiom (module-axioms-to-be-fixed module))))
	(error-operators (module-error-methods module)))
    (macrolet ((check-check (_eops)
		 ` (when (every #'(lambda (x)
				    #||
				    (and (memq x error-operators)
					 (not (method-is-user-defined-error-method
					       x)))
				    ||#
				    (memq x error-operators)
				    )
				,_eops)
		     (setq ,_eops nil))))
      ;;
      (if new-axiom
	  new-axiom
	(let* ((lhs (axiom-lhs axiom))
	       (lhs-e (term-error-operators&variables lhs nil))
	       (rhs (axiom-rhs axiom))
	       (rhs-e (term-error-operators&variables rhs nil))
	       (cond (axiom-condition axiom))
	       (cond-e (term-error-operators&variables cond nil)))
	  (when (and (or lhs-e rhs-e cond-e)
		     message?)
	    (when *chaos-verbose*
	      (with-output-chaos-warning ()
		(format t "axiom : ")
		(print-chaos-object axiom)
		(print-next)
		(format t "contains error operators."))))
	  ;; check 
	  (when *optimize-error-operators*
	    (check-check lhs-e)
	    (check-check rhs-e)
	    (check-check cond-e))
	  ;;
	  (if (or lhs-e rhs-e cond-e)
	      (let ((vars (mapcar #'(lambda (x) (cons x x)) (term-variables lhs))))
		(when lhs-e
		  (push (cons lhs
			      (or (cdr (assq lhs
					     (module-terms-to-be-fixed module)))
				  (setq lhs
				    (copy-term-using-variable lhs vars))))
			(module-terms-to-be-fixed module)))
		(when rhs-e
		  (push (cons rhs
			      (or (cdr (assq rhs
					     (module-terms-to-be-fixed module)))
				  (setq rhs
				    (copy-term-using-variable rhs vars))))
			(module-terms-to-be-fixed module)))
		(when cond-e
		  (push (cons cond
			      (or (cdr (assq cond
					     (module-terms-to-be-fixed module)))
				  (setq cond
				    (copy-term-using-variable cond vars))))
			(module-terms-to-be-fixed module)))
		(setq new-axiom
		  (make-rule :lhs lhs
			     :rhs rhs
			     :condition cond
			     :labels (axiom-labels axiom)
			     :type (axiom-type axiom)
			     :kind (axiom-kind axiom)
			     :no-method-computation t
			     :meta-and-or (axiom-meta-and-or axiom)))
		(push (cons axiom new-axiom)
		      (module-axioms-to-be-fixed module))
		new-axiom)
	    axiom))))))

;;;
;;; RECREATE-ERROR-AXIOM
;;;
(defun recreate-error-axiom (axiom module)
  (declare (type axiom axiom)
	   (type module module)
	   (values axiom))
  (let ((new-axiom (cdr (assq axiom (module-axioms-to-be-fixed module))))
	(error-operators (module-error-methods module)))
    (declare (type (or null axiom ) new-axiom)
	     (type list error-operators))
    (macrolet ((check-check (_eops)
		 ` (when (every #'(lambda (x)
				    #||
				    (and (memq x error-operators)
					 (not (method-is-user-defined-error-method
					       x)))
				    ||#
				    (memq x error-operators)
				    )
				,_eops)
		     (setq ,_eops nil))))
      ;;
      (if new-axiom
	  new-axiom
	  (let* ((lhs (axiom-lhs axiom))
		 (lhs-e (term-error-operators&variables lhs nil))
		 (rhs (axiom-rhs axiom))
		 (rhs-e (term-error-operators&variables rhs nil))
		 (cond (axiom-condition axiom))
		 (cond-e (term-error-operators&variables cond nil))
		 (terms-to-be-fixed nil)
		 )
	    (declare (type term lhs rhs cond)
		     (type list lhs-e rhs-e terms-to-be-fixed))
	    ;; check 
	    (when *optimize-error-operators*
	      (check-check lhs-e)
	      (check-check rhs-e)
	      (check-check cond-e))
	    ;;
	    (when (not (or lhs-e rhs-e cond-e))
	      (return-from recreate-error-axiom axiom))
	    ;;
	    (let ((vars (mapcar #'(lambda (x) (cons x x)) (term-variables lhs))))
	      (when lhs-e
		(setq lhs (copy-term-using-variable lhs vars))
		(push lhs terms-to-be-fixed))
	      (when rhs-e
		(setq rhs (copy-term-using-variable rhs vars))
		(push rhs terms-to-be-fixed))
	      (when cond-e
		(setq cond (copy-term-using-variable cond vars))
		(push cond terms-to-be-fixed))
	      ;;
	      (with-in-module (module)
		(let ((name (module-name module))
		      (op-map nil)
		      (sort-map nil))
		  (declare (type list op-map sort-map))
		  (cond ((int-instantiation-p name)
			 (let ((modmorph (views-to-modmorph
					  (int-instantiation-module name)
					  (int-instantiation-args name))))
			   (setq op-map (modmorph-op modmorph))
			   (setq sort-map (modmorph-sort modmorph))))
			((int-rename-p name)
			 (setq op-map (int-rename-op-maps name))
			 (setq sort-map (int-rename-sort-maps name))))
		  ;;
		  (dolist (term terms-to-be-fixed)
		    (replace-error-method module term op-map sort-map))))
	      ;;
	      (setq new-axiom
		    (make-rule :lhs lhs
			       :rhs rhs
			       :condition cond
			       :labels (axiom-labels axiom)
			       :type (axiom-type axiom)
			       :kind (axiom-kind axiom)
			       :no-method-computation t
			       :meta-and-or (axiom-meta-and-or axiom)))
	      new-axiom))))))

;;; EOF
