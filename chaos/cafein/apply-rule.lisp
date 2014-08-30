;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|=============================================================================
				  System:CHAOS
				 Module:cafein
			      File:apply-rule.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;; BASIC PROCS for REWRITE RULE APPLICATION ***********************************
;;;*****************************************************************************
;;; (defvar *rewrite-debug* nil)

;;; APPLY-RULE : rule term -> Bool
;;;-----------------------------------------------------------------------------
;;; Returns true iff the rule has been sucessfully apply. Note that in this case
;;; "term" is also modified. 
;;; The associative extensions are automatiquely generated and applied if needed.
;;;
(defun apply-rule (rule term)
  (declare (type axiom rule)
	   (type term term)
	   (values (or null t)))
  (let ((is-applied nil))
    (tagbody
       (when (rule-is-rule rule)
	 (if *rewrite-exec-mode*
	     (go do-apply)
	     (return-from apply-rule nil)))
       ;; rule is equation
       (when (and (not *cexec-normalize*)
		  (term-is-applform? term)
		  (method-has-trans-rule (term-head term)))
	 (return-from apply-rule nil))
       ;;---- 
     do-apply
       ;;----
       ;;
       ;; first apply the given rule.
       (setq is-applied (apply-one-rule rule term))

       ;; then there may be some extensions.
       (when (and (not is-applied) (term-is-applform? term))
	 (let ((top (term-method term)))
	   (declare (type method top))
	   (unless (let ((val (axiom-kind rule)))
		     (and val
			  (not (eq :id-theorem val))
			  (not (eq :idem-theory val))))
	     (when (method-is-associative top)
	       (if (method-is-commutative top)
		   (setq is-applied
			 (or (apply-AC-extension rule term top)
			     is-applied))
		   ;; the operator is only associative,
		   (setq is-applied
			 (or (apply-A-extensions rule term top)
			     is-applied))
		   )))))
       )
    ;; return t iff the rule is applied.
    is-applied))

;;;
;;; APPLY-ONE-RULE
;;;
(defun apply-one-rule (rule term)
  (declare (ignore rule term))
  (format t "~%APPLY-ONE-RULE : INTERNAL ERROR, SPECIFIC REWRITEING ENGINE ISN'T SPECIFIED.")
  (break))

(declaim (inline term-replace-dd-simple))
#-gcl
(defun term-replace-dd-simple (old new)
  (declare (type term old new)
	   (values term))
  (incf *rule-count*)
  (term-replace old new))

#+gcl
(si::define-inline-function term-replace-dd-simple (old new)
  (incf *rule-count*)
  (term-replace old new))

(defmacro beh-context-ok? (rule)
  ` (if *rewrite-semantic-reduce*
	(if (axiom-is-behavioural ,rule)
	    (check-beh-context)
	    t)
 	t))

(defun apply-one-rule-simple (rule term)
  (declare (type axiom rule)
	   (type term term)
	   (values (or null t)))
  (declare (inline term-replace-dd-simple))
  ;;
  (block the-end
    (let* ((condition nil)
	   next-match-method
	   (*self* term))
      (multiple-value-bind (global-state subst no-match E-equal)
	  (funcall (rule-first-match-method rule) (rule-lhs rule) term)
	(incf $$matches)
	(when no-match (return-from the-end nil))

	;;
	(unless (beh-context-ok? rule)
	  (return-from the-end nil))
	;;
	;; technical assignation related to substitution-image.
	(when E-equal (setq subst nil))

	;; match success -------------------------------------
	;; then, the condition must be checked
	(block try-rule
	  (catch 'rule-failure
	    ;;
	    (when (and (is-true? (setq condition (rule-condition rule)))
		       (null (rule-id-condition rule)))
	      ;; there is no condition --
	      ;; rewrite term.
	      (term-replace-dd-simple
	       term
	       ;; note that the computation of the substitution
	       ;; made a copy of the rhs.
	       (substitution-image-simplifying subst
					       (rule-rhs rule)))
	      (return-from the-end t))))

	;; if the condition is not trivial, we enter in a loop
	;; where one try to find a match such that the condition 
	;; is satisfied.
	(setf next-match-method (rule-next-match-method rule))
	(loop (when no-match (return))
	      (unless (beh-context-ok? rule)
		(return-from the-end nil))
	      (block try-rule
		(catch 'rule-failure
		  (if (and (or (null (rule-id-condition rule))
			       (rule-eval-id-condition subst
						       (rule-id-condition rule)))
			   (is-true?
			    (let (($$cond (substitution-image subst condition))
				  (*rewrite-exec-mode*
				   (if *rewrite-exec-condition*
				       *rewrite-exec-mode*
				       nil)))
			      ;; no simplyfing since probably wouldn't pay
			      (if *rewrite-semantic-reduce*
				  (normalize-term-with-bcontext $$cond)
				  (normalize-term $$cond))
			      $$cond)))
		      ;; the condition is satisfied
		      (progn
			(term-replace-dd-simple
			 term
			 (substitution-image-simplifying subst
							 (rule-rhs rule)))
			(return-from the-end t))
		      nil)))
	      
	      ;; else, try another ...
	      (multiple-value-setq (global-state subst no-match)
		(progn
		  (incf $$matches)
		  (funcall next-match-method global-state)
		  ))

	      );; end loop
	
	;; In this case there is no match at all and the rule does not apply.
	(return-from the-end nil)))))

;;; INIT
(eval-when (:execute :load-toplevel)
  (setf (symbol-function 'apply-one-rule)
	(symbol-function 'apply-one-rule-simple)))

;;; APPLY-A-EXTENSIONS : rule term method -> Bool
;;;-----------------------------------------------------------------------------
;;; Apply the associative-extensions. returns true iff the some rule is applied.
;;;
(defun apply-A-extensions (rule term top)
  (declare (type axiom rule)
	   (type term term)
	   (type method top)
	   (values (or null t)))
  ;; (declare (optimize (speed 3) (safety 0)))
  (let ((listext (!axiom-a-extensions rule))
	(a-ext nil)
	(is-applied nil))
    (when (null listext)
      ;; then need to pre-compute the extensions and store then
      (setq listext (compute-A-extensions rule top)))
    (when (setq a-ext (car listext))
      ;; the first extension exists
      (setq is-applied (apply-one-rule a-ext term)))
    (setq listext (cdr listext))
    (when (setq a-ext (car listext))
      ;; the second extension exists
      (setq is-applied (or (apply-one-rule a-ext term)
			   is-applied)))
    (setq listext (cdr listext))
    (when (setq a-ext (car listext))
      ;; the third extension exists
      (setq is-applied (or (apply-one-rule a-ext term)
			   is-applied)))
    ;;
    is-applied))

;;; APPLY-AC-EXTENSION : rule term method -> Bool
;;;-----------------------------------------------------------------------------
;;; Apply the associative-commutative-extension. returns t iff the rule is applied.
;;;
(defun apply-AC-extension (rule term top)
  (declare (type axiom rule)
	   (type term term)
	   (type method top)
	   (values (or null t)))
  (let ((listext (give-AC-extension rule))
	(is-applied nil))
    (when (car listext)
      ;; the extension exists
      (setq is-applied (apply-one-rule (car listext) term)))
    is-applied))

;;; RULE-EVAL-ID-CONDITION : substitution condition ->
;;;-----------------------------------------------------------------------------
;;; really not not want to use normalize -- perhaps could use normal expressions.
(defun rule-eval-id-condition (subst cond)
  (declare (type list subst cond)
	   (values (or null t)))
  (cond ((eq 'and (car cond))
	 (dolist (sc (cdr cond) t)
	   (unless (rule-eval-id-condition subst sc) (return nil))))
	((eq 'not-equal (car cond))
	 (not (term-is-similar?
	       (rule-eval-term subst (cadr cond))
	       (rule-eval-term subst (caddr cond)))))
	((eq 'equal (car cond))
	 (term-is-similar?
	  (rule-eval-term subst (cadr cond))
	  (rule-eval-term subst (caddr cond))))
	((eq 'or (car cond))
	 (dolist (sc (cdr cond) nil)
	   (when (rule-eval-id-condition subst sc) (return t))))
	((eq 'not (car cond))
	 (not (rule-eval-id-condition subst (cadr cond))))
	((eq 'xor (car cond))		;@@ remove?
	 (let ((res nil))
	   (dolist (sc (cdr cond))
	     (setq res (if (rule-eval-id-condition subst sc) (not res) res)))
	   res))
	(t (break "rule-eval-id-condition: illegal condition"))
	))

;;; RULE-EVAL-TERM : teta term -> term'
;;;
(defun rule-eval-term (teta term)
  (declare (type list teta)
	   (type term term)
	   (values list))
  (macrolet ((assoc% (_x _y)
	       `(let ((*_lst ,_y))
		 (loop
		  (when (null *_lst) (return nil))
		  (when (eq ,_x (caar *_lst)) (return (car *_lst)))
		  (setq *_lst (cdr *_lst))))))
    (cond ((term-is-variable? term)
	   (let ((im (cdr (assoc% term teta))))
	     (if im;; i.e. im = teta(term)
		 im
		 ;; if variable doesn't have a binding, it evaluates to itself
		 term)))
	  (t term))))

;;; EOF
