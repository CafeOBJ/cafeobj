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
				  Module:tools
			       File:op-check.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;; CHECK TOOLS FOR OPERATORS
;;;*****************************************************************************

;;; **************************
;;; LAZYNESS(STRICTNESS) CHECK
;;; **************************
;;; CHECK-METHOD-STRINCTNESS method : -> Bool
;;;
;;; 1. constants(operations free from axioms) are always strict.
;;; 
(defun check-method-strictness (meth &optional
				     (module (or *current-module*
						 *last-module*
						 ))
				     report?)
				     
  (unless module
    (with-output-chaos-error ('no-cntext)
      (princ "checking lazyness: no context module is specified!")
      ))
  ;;
  (with-in-module (module)
    (cond ((and (null (method-rules-with-different-top meth))
		(rule-ring-is-empty (method-rules-with-same-top meth)))
	   ;; the method has no rewrite rules
	   (if report?
	       (show-method-strictness-report meth
					      (butlast (the-default-strategy
							(length (method-arity meth))))
					      nil)
	       (values (butlast (the-default-strategy (length (method-arity meth))))
		       nil)))
	  ;; the method has some rewrite rules associated with it.
	  ((or
	    ;; has some equational theory
	    (not (theory-is-empty-for-matching (method-theory meth)))
	    ;; the method is not free constructor.
	    (null (method-rules-with-different-top meth))
	    ;; has rules with different top and constant
	    ;; --> non-free constructor
	    (null (method-arity meth)))
	   ;; then the strategy is bottom up:
	   (if report?
	       (show-method-strictness-report
		meth
		(butlast (the-default-strategy
			  (length (method-arity meth))))
		nil)
	       (values (butlast (the-default-strategy (length (method-arity meth))))
		       nil)))
	  ;;
	  (t
	   ;; the real work begins here.
	   (let ((l-ar (length (method-arity meth)))
		 (strategy nil)
		 (end-strategy nil))
	     (do ((occ 0 (1+ occ)))
		 ((<= l-ar occ))
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
		 ;; method is maximal. can delay the evaluation.
		 (push (1+ occ) end-strategy)
		 ))
	     ;;
	     (if report?
		 (show-method-strictness-report meth
						(reverse strategy)
						(reverse end-strategy))
		 (values (reverse strategy) (reverse end-strategy)))))
	  )))

(defun check-operator-strictness (op &optional (module (or *last-module*
							    *current-module*))
				     report?)
  (unless module
    (with-output-chaos-error ('no-context)
      (princ "no context (current) module is given!")
      ))
  ;;
  (let* ((opinfo (if (opinfo-p op)
		     (prog1 op (setq op (opinfo-operator op)))
		     (get-operator-info op (module-all-operators module))))
	 (methods (opinfo-methods opinfo))
	 (res nil))
    (when report?
      (print-next)
      (let ((*print-line-limit* 60))
	(format t "~%------------------------------------------------------------")
	(print-next)
	(print-centering
	 (format nil "* laziness of operator: ~a *" (operator-symbol op)))))
    ;;
    (dolist (meth methods)
      (unless (method-is-error-method meth)
	(multiple-value-bind (str-list1 str-list2)
	    (check-method-strictness meth module)
	  (when report?
	    (with-in-module (module)
	      (print-next)
	      (format t "------------------------------------------------------------")
	      (show-method-strictness-report meth
					     str-list1
					     str-list2)))
	  (push (list meth str-list1 str-list2) res))))
    (nreverse res)))

(defun check-operator-strictness-whole (&optional (module (or *last-module*
							      *current-module*))
						  report?)
  (unless module
    (with-output-chaos-error ('no-context)
      (princ "no context (current) module is specified!")
      ))
  ;;
  (let ((result nil))
    (dolist (opinfo (ops-to-be-shown module))
      (let ((op (opinfo-operator opinfo))
	    (res nil))
	(setq res (check-operator-strictness op module report?))
	(push (cons op res) result)))
    (nreverse result)))
      
(defun show-method-strictness-report (method sl1 sl2)
  (print-next)
  (print-chaos-object method)
  (let ((*print-indent* (+ 2 *print-indent*))
	(strategy (or (method-rewrite-strategy method)
		      (method-supplied-strategy method)
		      (operator-strategy (method-operator method)))))
    (cond ((and (null sl1) (null sl2))
	   (print-next)
	   (princ "* NON-STRICT (lazy)."))
	  (t (when sl1
	       (print-next)
	       (format t "* strict on the arguments : ~{~^ ~a~}" sl1))
	     (when sl2
	       (print-next)
	       (format t "* may delay the evaluation on the arguments : ~{~^ ~a~}" sl2))))
    ;;
    (print-next)
    (if strategy
	(format t "- rewrite strategy:~{~^ ~a~}" strategy)
	(princ "- rewrite strategy: none"))
    (let ((axioms (method-all-rules method)))
      (when axioms
	(print-next)
	(princ "- axioms:")
	(let ((*print-indent* (+ 2 *print-indent*)))
	  (dolist (rl axioms)
	    (print-next)
	    (print-axiom-brief rl)))))))




;;; ***************************************************************************
;;; COHERENCY CHECK
;;; ***************************************************************************

(defun method-contained-in (meth term)
  (cond ((term-is-constant? term) nil)
	(t (let ((head (term-head term)))
	     (when (method-is-of-same-operator meth head)
	       (return-from method-contained-in t))
	     (dotimes (x (length (term-subterms term)))
	       (when (method-contained-in meth (term-arg-n term x))
		 (return-from method-contained-in t)))
	     nil))))

(defun check-method-coherency (meth &optional
				    (module (or *current-module* *last-module*))
				    (warn t))
  (unless module
    (with-output-chaos-error ('no-cntext)
      (princ "checking coherecy: no context module is specified!")))
  ;;
  (when (or (method-is-of-same-operator meth *beh-equal*)
	    (method-is-of-same-operator meth *beh-eq-pred*))
    (when warn
      (with-output-chaos-warning ()
	(princ "specified operator is special built-in predicate.")))
    (return-from check-method-coherency nil))
  ;;
  (let ((methods (module-beh-methods module))
	(attrs (module-beh-attributes module))
	(hs (dolist (x (method-arity meth))
	      (when (sort-is-hidden x)
		(return x)))))
    (declare (type list methods attrs))
    ;;
    (unless (sort-p hs)
      (when warn
	(with-output-chaos-warning ()
	  (princ "operator ")
	  (print-chaos-object meth)
	  (princ " has no hidden sort argument.")))
      (return-from check-method-coherency nil))
    (when (sort= *huniversal-sort* hs)
      (when warn
	(with-output-chaos-warning ()
	  (princ "specified operator is special built-in.")))
      (return-from check-method-coherency nil))
    (when (method-is-behavioural meth)
      (when warn
	(with-output-chaos-warning ()
	  (princ "operator ")
	  (print-chaos-object meth)
	  (princ " is declared as behavioural.")))
      (return-from check-method-coherency nil))
    (unless (sort-is-hidden (method-coarity meth))
      (format t "~%**> operator: ")
      (print-chaos-object meth)
      (format t "~%   is trivially behaviouraly coherent.")
      (return-from check-method-coherency t))
    ;;
    (with-in-module (module)
      ;;
      (let ((observers nil))
	(dolist (op (append methods attrs))
	  (when (find-if #'(lambda (x) (sort<= hs x))
			 (method-arity op))
	    (push op observers)))
	;;
	(format t "~%**> starting coherence check of ")
	(print-chaos-object meth)
	;;
	(unless observers
	  (format t "~% no context constructing operations,")
	  (format t "~% failed to prove coherency.")
	  (return-from check-method-coherency nil))
	;;
	(let* ((con-count 0)
	       ;; op(x1,...xn)
	       (op-pat (make-term-with-sort-check
			meth
			(mapcar #'(lambda (x)
				    (make-variable-term x
							(gensym "X")))
				(method-arity meth)))))
	  (dolist (ob observers)
	    (let* ((hs-var (make-variable-term hs (gensym "HS")))
		   ;; ob(cv1,...,zi,..,cvn)
		   (context-pat (make-term-with-sort-check
				 ob
				 (mapcar #'(lambda (x)
					     (if (sort-is-hidden x)
						 ;; op-pat
						 hs-var
						 (make-variable-term
						  x
						  (gensym "CV"))))
					 (method-arity ob)))))
	      (format t "~%-- context pattern(~d): " (incf con-count))
	      (print-chaos-object context-pat)
	      ;;
	      (let ((ax nil)
		    (match? nil)
		    (subst nil)
		    (checked? nil)
		    (found? nil))
		;;
		(dolist (x (method-rules ob))
		  (setq found? nil)
		  (multiple-value-setq (match? subst)
		    (perform-context-match (axiom-lhs x)
					   context-pat
					   ))
		  (when match?
		    (setq ax x)
		    (if (method-contained-in meth (axiom-lhs ax))
			(progn
			  (setq subst nil)
			  (setq found? t)
			  ;;
			  (format t "~%   * found an axiom : ")
			  (print-chaos-object ax))
			;;
			(let ((image (variable-image subst hs-var))
			      (new-lhs nil)
			      (new-rhs nil)
			      (new-cond (axiom-condition ax))
			      )
			  (when (and image (term-is-psuedo-constant? image))
			    (setq found? t)
			    (setq subst
				  (substitution-add (new-substitution)
						    image
						    op-pat))
			    ;;
			    (format t "~%   * found an axiom : ")
			    (print-chaos-object ax)
			    (when subst
			      (format t "~%   with substitution: ")
			      (print-substitution subst))
			    ;;
			    (setq new-lhs
				  (substitution-image2 subst
						       (axiom-lhs ax)))
			    (setq new-rhs
				  (substitution-image2 subst
						       (axiom-rhs ax)))
			    (unless (is-true? (axiom-condition ax))
			      (setq new-cond
				    (substitution-image2
				     subst
				     (axiom-condition ax))))
			    ;;
			    (setq ax
				  (make-rule :lhs new-lhs
					     :rhs new-rhs
					     :condition new-cond
					     :behavioural (axiom-behavioural ax)
					     :id-condition (axiom-id-condition ax)
					     :type (axiom-type ax)
					     :kind (axiom-kind ax)
					     :labels (axiom-labels ax)
					     :meta-and-or (axiom-meta-and-or ax)))
			    (when *chaos-verbose*
			      (format t "~%   -- check with axiom instance:")
			      (format t "~%   ")
			      (print-chaos-object ax))
			    )))
		    ;;
		    ;;
		    (when found?
		      (setq checked? t)
		      ;;
		      (unless (is-true? (axiom-condition ax))
			(format t "~%  axiom is conditional,")
			(format t "~%  system can not check coherency, sorry!")
		      (return-from check-method-coherency nil))
		      ;;
		      ;; RHS
		      ;;
		      (format t "~%   -- start checking rhs pattern : ")
		      (let ((ng? (check-def-rhs meth (axiom-rhs ax) subst 1)))
			(when ng?
			  (return-from check-method-coherency nil))
			(format t "~%   * success."))
		      )))
		;;
		(unless checked?
		  (format t "~%   * no axioms of context pattern,")
		  (format t "~%   failed to prove.")
		  (return-from check-method-coherency nil))
		)
	      ))
	  ;; all done
	  (format t "~%** operator is behaviourally coherent.")
	  t
	  )))))
		
(defun perform-context-match (target pattern)
  (flet ((matcher (pat term)
	   (if (term-is-variable? pat)
	       (if (sort<= (term-sort term) (variable-sort pat)
			   (module-sort-order *current-module*))
		   (values nil (list (cons pat term)) nil nil)
		   (values nil nil t nil))
	       (if (term-is-lisp-form? pat)
		   (values nil nil t nil)
		   (first-match pat term)))))
    ;;
    (let ((real-target (supply-psuedo-variables target)))
      ;; ---- first match 
      (multiple-value-bind (global-state subst no-match e-equal)
	  (matcher pattern real-target)
	(declare (ignore global-state))
	(when no-match
	  (return-from perform-context-match nil))
	(when e-equal
	  (when *chaos-verbose*
	    (format t "~&-- terms are equational equal."))
	  (return-from perform-context-match (values t nil)))
	;;
	#||
	(when *chaos-verbose*
	  (format t "~%* match success with substitution : ")
	  (let ((*print-indent* (+ *print-indent* 4)))
	    (print-substitution subst)))
	||#
	(values t subst)))))

(defvar .op-found. 0)

(defun check-def-rhs (meth rhs subst context-depth)
  (setq .op-found. 0)
  (let* ((rhs-inst (substitution-image2 subst rhs))
	 (res (check-def-rhs* meth rhs-inst context-depth nil)))
    (when (< 1 .op-found.)
      (format t "~%* operator ")
      (print-chaos-object meth)
      (format t "~%occurs more than once on RHS."))
    res))

(defun check-def-rhs* (meth rhs context-depth occurrence)
  (cond ((term-is-constant? rhs)	; includes vars, psude vars, lisp,
					; built-in constants also.
	 nil)
	(t (let ((head (term-head rhs)))
	     ;; (format t "~%RHS =")
	     ;; (term-print rhs)
	     ;; ---------------------------------------
	     (when (eq *bool-if* head)
	       (return-from check-def-rhs* nil))
	     ;; ^^^^^^^^-------------------------------
	     #||
	     (when (some #'(lambda (x) (sort-is-hidden x))
			 (method-arity head))
	       (when (and (not (method-is-behavioural head))
			  (not (eq *bool-if* head))
			  (not (method-is-of-same-operator meth
							   head)))
		 (format t "~%   * contains non behavioural operator with hidden sort argument.")
		 (terpri)
		 (print-chaos-object head)
		 (format t "~%* failed to prove.")
		 (return-from check-def-rhs* :ng1)))
	     ||#
	     (when (method-is-of-same-operator meth head)
	       (incf .op-found.)
	       (unless (>= context-depth (length occurrence))

		 (format t "~%   * for operator: ")
		 (print-chaos-object meth)
		 (print-next)
		 (princ "    rhs = ")
		 (term-print rhs)

		 (format t "~%   * could not find monotonic, well-founded ordering.")
		 (format t "~%     operator occurs at ~a"
			 (mapcar #'(lambda (x) (1+ x))
				 (reverse occurrence)))
		 (return-from check-def-rhs* :ng2)))
	     (dotimes (x (length (term-subterms rhs)))
	       (let ((ng (check-def-rhs* meth
					 (term-arg-n rhs x)
					 context-depth
					 (cons x occurrence))))
		 (when ng
		   (return-from check-def-rhs* ng))))
	     ;;
	     nil			; OK
	     ))))
  
(defun check-operator-coherency (op
				 &optional
				 (module (or *current-module* *last-module*))
				 (warn t)
				 )
				 
  (unless module
    (with-output-chaos-error ('no-context)
      (princ "no context (current) module is given!")
      ))
  ;;
  (let* ((opinfo (if (opinfo-p op)
		     (prog1 op (setq op (opinfo-operator op)))
		     (get-operator-info op (module-all-operators module))))
	 (methods (opinfo-methods opinfo)))
    (dolist (meth methods)
      (when (or (method-is-user-defined-error-method meth)
		(not (method-is-error-method meth)))
	(check-method-coherency meth module warn)))
    ))

(defun check-operator-coherency-whole (mod)
  (with-in-module (mod)
    (let ((ops (module-all-operators mod)))
      (dolist (opinfo ops)
	(let ((methods (opinfo-methods opinfo)))
	  (dolist (meth methods)
	    (when (or (method-is-user-defined-error-method meth)
		      (not (method-is-error-method meth)))
	      (check-method-coherency meth mod nil))))))))

;;; CONGRUENCE CHECK
;;; may modify operator's attribute.
;;;
(defun check-operator-congruency (mod)
    (let ((ops nil)
	  (cong nil)
	  (nocong nil)
	  (cobasis nil)
	  (observers nil))
      (when (eq 'void *beh-equal*) (return-from check-operator-congruency nil))
      (when *beh-proof-in-progress* (return-from check-operator-congruency nil))
      ;;
      (with-in-module (mod)
	(dolist (op (module-beh-methods mod))
	  (if (method-arity op)
	      (if (method-rules op)
		  (push op observers)
		(push op ops))
	    (push op cong)))
	(dolist (op (module-beh-attributes mod))
	  (if (method-rules op)
	      (push op observers)
	    (push op ops)))
	(dolist (op (module-non-beh-methods mod))
	  (if (method-arity op)
	      (if (method-rules op)
		  (push op observers)
		(push op ops))
	    (push op cong)))
	(dolist (op (module-non-beh-attributes mod))
	  (unless (method-is-of-same-operator op *beh-equal*)
	    (if (method-rules op)
		(push op observers)
	      (push op ops)))))
      ;;
      (dolist (op ops)
	(if (check-method-congruency op observers mod)
	    (push op cong)
	  (push op nocong)))
      ;;
      (setq cobasis (nconc observers nocong))
      ;;
      (with-in-module (mod)
	(dolist (op cong)
	  (cond ((method-is-behavioural op)
		 (when *chaos-verbose*
		   (with-output-msg ()
		     (princ "operator ")
		     (print-chaos-object op)
		     (print-next)
		     (princ "is need not be declared as bop.")
		     )))
		(t (when (method-arity op)
		     ;; (setf (method-is-coherent op) t)
		     (unless (method-is-coherent op)
		       (with-output-simple-msg ()
			 (princ "** system found the operator")
			 (print-next)
			 (print-chaos-object op)
			 (print-next)
			 (princ "can be declared as coherent.")))))
		))
	(setf (module-cobasis mod) cobasis)
	)
      ))
	
(defun check-method-congruency (meth iobservers
				&optional (module (or *current-module*
						      *last-module*)))
  (unless module
    (with-output-panic-message ()
      (princ "congruence check: no context module!")))
  (let ((hs (method-coarity meth)))
    (unless (sort-is-hidden hs)
      (return-from check-method-congruency nil))
    (when (sort= *huniversal-sort* hs)
      (with-output-chaos-warning ()
	(princ "specified operator is special built-in."))
      (return-from check-method-congruency nil))
    ;;
    (with-in-module (module)
      (let ((observers nil))
	(dolist (op iobservers)
	  (when (find-if #'(lambda (x) (sort<= hs x))
			 (method-arity op))
	    (push op observers)))
	(unless observers
	  (return-from check-method-congruency nil))
	(dolist (ob observers)
	  (let ((found nil))
	    (dolist (rule (method-rules ob))
	      (let ((lhs (axiom-lhs rule))
		    (subst-var nil)
		    (rhs (axiom-rhs rule)))
		(multiple-value-bind (occ-l num-if-l)
		    (find-occ lhs
			      #'(lambda (x)
				  (and (term-is-applform? x)
				       (method-is-of-same-operator
					(term-head x)
					meth)))
			      nil
			      0)
		  (multiple-value-bind (occ-r num-if-r)
		      (find-occ rhs
				#'(lambda (x)
				    (and (term-is-applform? x)
					 (method-is-of-same-operator
					  (term-head x)
					  meth)))
				nil
				0)
		    (unless (listp occ-l)
		      (multiple-value-setq (occ-l num-if-l)
			(find-occ lhs 
				  #'(lambda (x)
				      (and (term-is-variable? x)
					   (sort<= (method-coarity meth)
						   (term-sort x))
					   (setq subst-var x)))
				  nil
				  0)))
		    (when (and occ-l (not (listp occ-r)) subst-var)
		      (multiple-value-setq (occ-r num-if-r)
			(find-occ rhs
				  #'(lambda (x)
				      (and (term-is-variable? x)
					   (variable= x subst-var)))
				  nil
				  0)))
		    
		    (when (and (listp occ-l)
			       (or (not (listp occ-r))
				   ;; (<= (length occ-r) (length occ-l))
				   (<= (- (length occ-r) num-if-r) (length occ-l))
				   ))
		      (setq found t)
		      (return t))))))	; done for all rules of an observer
	    (unless found
	      (return-from check-method-congruency nil))))
	;; done for all
	t))))
;;;
;;;
;;;
(defun substitution-image2 (sigma term)
  (declare (type list sigma)
	   (type term))
  (let ((*consider-object* t))
    (cond ((or (term-is-variable? term)
	       (term-is-psuedo-constant? term))
	   (let ((im (variable-image-slow sigma term)))
	     (if im
		 (values im (sort= (variable-sort term)
				   (term-sort im)))
		 (values term t))))
	  ((term-is-builtin-constant? term) term)
	  ((term-is-lisp-form? term)
	   (multiple-value-bind (new success)
	       (funcall (lisp-form-function term) sigma)
	     (if success
		 new
		 term)))
	  ((term-is-applform? term)
	   (let ((l-result nil)
		 (modif-sort nil))
	     (dolist (s-t (term-subterms term))
	       (multiple-value-bind (image-s-t same-sort)
		   (substitution-image2 sigma s-t)
		 (unless same-sort (setq modif-sort t))
		 (push image-s-t l-result)))
	     (setq l-result (nreverse l-result))
	     (let ((method (term-head term)))
	       (if (and (cdr l-result)
			(null (cddr l-result))
			(method-is-identity method))
		   ;; head operator is binary & has identity theory
		   (if (term-is-zero-for-method (car l-result) method)
		       ;; ID * X --> X
		       ;; simplify for left identity.
		       (values (cadr l-result)
			       (sort= (term-sort term)
				      (term-sort (cadr l-result))))
		       ;; X * ID --> X
		       (if (term-is-zero-for-method (cadr l-result) method)
			   (values (car l-result)
				   (sort= (term-sort term)
					  (term-sort (car l-result))))
			   ;; X * Y 
			   (if modif-sort
			       (let ((term-image (make-term-with-sort-check 
						  method l-result)))
				 (values term-image
					 (sort= (term-sort term)
						(term-sort term-image))))
			       (values (make-applform (term-sort term)
						      method l-result)
				       t) ; sort not changed
			       )))	; done for zero cases
		   ;; This is the same as the previous bit of code
		   (if modif-sort
		       (let ((term-image (make-term-with-sort-check method
								    l-result)))
			 (values term-image
				 (sort= (term-sort term) (term-sort term-image))))
		       (values (make-applform (method-coarity method)
					      method l-result)
			       t))))))
	  (t (break "not implemented yet"))
	  )))
;;; EOF
