;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: rwl.lisp,v 1.2 2010-07-30 02:26:47 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: construct
				 File: rwl.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; stuff supporting proof in rewriting logic.
;;;
(defun make-congruence-axiom (opinfo module)
  (let ((var-num 0)
	l-arg1
	l-arg2
	lhs
	rhs-subs
	rhs)
    (declare (type fixnum var-num))
    ;;
    ;; if "oper" is 2-ary operator, then creates the following equation:
    ;; eq oper(t1,t2) ==> oper(t1',t2') = (t1 ==> t2) and (t1' ==> t2')
    ;; ceq oper(t1,t2) ==> oper(t1',t2') = true if (t1 ==> t2) and (t1' ==> t2').
    ;;
    (let ((methods (opinfo-methods opinfo))
	  (ms nil)
	  (result nil))
      (unless (method-arity (car methods))
	(return-from make-congruence-axiom nil)) ; this case is handled by
						 ; builtin axiom for _==>_.
      (when (some #'(lambda (x) (method-is-universal* x))
		  methods)
	(return-from make-congruence-axiom nil))
      ;;
      (dolist (m methods)
	(let ((pmeth nil))
	  (block next-method
	    (when (or (method-is-error-method m)
		      (module-is-hard-wired (method-module m))
		      (method-is-behavioural m)
		      (sort-is-hidden (method-coarity m)))
	      (return-from next-method nil))
	    (setq pmeth (method-most-general-no-error m methods module))
	    (unless (memq pmeth ms)
	      (push pmeth ms)))))
      ;; ms contains most general methods
      (dolist (method ms)
	(block next-method
	  (when (memq method (module-methods-with-rwl-axiom module))
	    (return-from next-method nil))
	  (push method (module-methods-with-rwl-axiom module))
	  (let ((vars1 (mapcar #'(lambda (x)
				   (make-variable-term
				    x
				    (intern (format nil "cv~d" (incf var-num)))))
			       (method-arity method)))
		(vars2 (mapcar #'(lambda (x)
				   (make-variable-term
				    x
				    (intern (format nil "cv~d" (incf var-num)))))
			       (method-arity method))))
	    ;;
	    (setq l-arg1
		  (make-term-with-sort-check method vars1 module))
	    (setq l-arg2
		  (make-term-with-sort-check method vars2 module))
	    (setq lhs
		  (make-term-with-sort-check *rwl-predicate*
					     (list l-arg1 l-arg2)
					     module))
	    (setq rhs-subs
		  (mapcar #'(lambda (x y)
			      (make-term-with-sort-check *rwl-predicate*
							 (list x y)
							 module))
			  vars1
			  vars2))
	    (setq rhs (reduce #'(lambda (x y)
				  (make-term-with-sort-check *bool-and*
							     (list x y)))
			      rhs-subs))
	    (push
	     (make-rule :lhs lhs
			:rhs *bool-true*
			:condition rhs
			:type :equation
			:kind ':rwl-congruence)
	     result)
	    )))
      ;;
      result)))

(defun make-trans-relations (rule module)
  (when (rule-is-builtin rule)
    (return-from make-trans-relations nil))
  (let ((l-arg1 (rule-lhs rule))
	(l-arg2 (rule-rhs rule))
	(cond (rule-condition rule))
	lhs)
    (setq lhs
	  (make-term-with-sort-check *rwl-predicate*
				     (list l-arg1 l-arg2)
				     module)
	  )
    (make-rule :lhs lhs
	       :rhs *bool-true*		; (if cond cond *bool-true*)
	       :condition (if cond cond *bool-true*) ; was *bool-true*
	       :type ':equation
	       :kind ':rwl-transition
	       :labels nil)))

#||
(defun add-rwl-axioms (module)
  (flet ((trans-rule (rule)
	   (unless (member rule (module-rules-with-rwl-axiom module)
			   :test #'rule-is-similar?)
	     (let ((ax (make-trans-relations rule module)))
	       (when ax
		 (adjoin-axiom-to-module module ax)
		 (push ax (module-rules-with-rwl-axiom module)))))
	   ))
    ;;
    (unless (module-includes-rwl module)
      (return-from add-rwl-axioms nil))
    ;; 
    (with-in-module (module)
      ;; add congruence rule for ==>, one for each operator:
      (dolist (opinfo (module-all-operators module))
	(let ((axs (make-congruence-axiom opinfo module)))
	  (dolist (ax axs)
	    (adjoin-axiom-to-module module ax))))
      ;; add axiom of ==> for each rule in module.
      (let ((tobe-fixed (module-axioms-to-be-fixed module)))
	(dolist (rul (module-rules module))
	  (when (eq (axiom-type rul) :rule)
	    (setq rul (or (cdr (assq rul tobe-fixed)) rul))
	    (trans-rule rul)))
	(dolist (rul (module-rewrite-rules module))
					; because we called even when the own
					; rewrite rules are not yet set up.
	  (when (eq (axiom-type rul) :rule)
	    (setq rul (or (cdr (assq rul tobe-fixed)) rul))
	    (trans-rule rul))))
      )))
||#

(defun add-rwl-axioms (module)
  (declare (ignore module))
  nil)

;;; EOF
