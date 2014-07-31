;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
(in-package :chaos)
#|=============================================================================
				    System:CHAOS
				   Module:thstuff
			        File:apply-tactic.lisp
 =============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;; if true, a tactic is applied to all unproved goals
;;; 
(defvar *apply-in-automatic* nil)

;;;
;;; with-in-context : ptree-node
;;; construct a lexical environment for applying a tactic.
;;;
(eval-when (:compile-toplevel :execute :load-toplevel)
(defmacro with-in-context ((ptree-node) &rest body)
  (once-only (ptree-node)
    `(block :exit
       (let* ((.cur-goal. (ptree-node-goal ,ptree-node))
	      (.cur-targets. (goal-targets .cur-goal.))
	      (.next-goals. nil))
	 (unless .cur-targets. (return-from :exit nil))
	 ,@body))))
)

;;; ==============
;;; some utilities
;;; ==============

(defun rule-copy-canonicalized (rule module)
  (let* ((new-rule (rule-copy rule))
	 (canon (canonicalize-variables (list (rule-lhs new-rule)
					      (rule-rhs new-rule)
					      (rule-condition new-rule))
					module)))
    (setf (rule-lhs new-rule) (first canon)
	  (rule-rhs new-rule) (second canon)
	  (rule-condition new-rule) (third canon))
    new-rule))


;;; 
;;; IMPLICATION[IP]
;;; **********************
(defun apply-ip (ptree-node)
  (declare (type ptree-node ptree-node))
  ;; normalize
  (apply-rd ptree-node)
  ;;
  (with-in-context (ptree-node)
    (dolist (target .cur-targets.)
      (let ((cond (rule-condition target)))
	(unless (or (is-true? cond) (term-variables cond))
	  (let ((next-goal (prepare-next-goal ptree-node)))
	    (with-in-module ((goal-context next-goal))
	      (let ((new-ax (make-rule :lhs (term-copy-and-returns-list-variables cond)
				       :rhs *bool-true*
				       :id-condition *bool-true*
				       :type (axiom-type target)
				       :behavioural (axiom-is-behavioural target)
				       :first-match-method (axiom-first-match-method target)
				       :next-match-method (axiom-next-match-method target)
				       :labels (cons "[ip]" (axiom-labels target))
				       :kind (axiom-kind target)
				       :meta-and-or (axiom-meta-and-or target)))
		    (new-target (rule-copy-canonicalized target *current-module*)))
		(setf (rule-condition new-target) *bool-true*)
		(setf (goal-targets next-goal) (list new-target))
		(push next-goal .next-goals.)
		(compute-rule-method new-ax)
		(adjoin-axiom-to-module *current-module* new-ax)
		(!setup-reduction *current-module*)))))))
    (if .next-goals.
	(values t .next-goals.)
      (values nil nil))))

;;; ================================
;;; TACTIC: Theory of Constants [TC]
;;; ================================

(defun make-tc-var-subst (module name variable)
  (multiple-value-bind (op meth)
      (declare-operator-in-module (list name)
				  nil	; we make constant
				  (variable-sort variable)
				  module
				  nil	; constructor?
				  nil	; behavioural? always nil.
				  nil   ; not coherent
				  )
    (declare (ignore op))
    (prepare-for-parsing module)
    (cons variable (make-applform-simple (variable-sort variable) meth nil))))
			  
(defun make-tc-const-name (ptree)
  (format nil "#C~d" (incf (ptree-num-gen-const ptree))))

(defun make-tc-variable-substitutions (ptree module vars)
  (declare (type ptree ptree)
	   (module module)
	   (list vars))
  (let ((subst nil))
    (dolist (var vars)
      (push (make-tc-var-subst module (make-tc-const-name ptree) var)
	    subst))
    subst))

(defun axiom-variables (ax)
  (let ((lhs (axiom-lhs ax))
	(rhs (axiom-rhs ax))
	(cond (axiom-condition ax)))
    (union (term-variables lhs) (union (term-variables rhs) (if cond (term-variables cond) nil) :test #'equal)
	   :test #'equal)))

(defun apply-tc (ptree-node)
  (declare (type ptree-node ptree-node))
  ;; internally apply-rd
  (apply-rd ptree-node)
  ;;
  (with-in-context (ptree-node)
    ;; do TC
    (dolist (cur-target .cur-targets.)
      (when (axiom-variables cur-target)
	(let ((next-goal (prepare-next-goal ptree-node)))
	  (with-in-module ((goal-context next-goal))
	    (let* ((next-target (rule-copy-canonicalized cur-target *current-module*))
		   (vars (axiom-variables next-target))
		   (subst (make-tc-variable-substitutions *proof-tree* *current-module* vars))
		   (new-ops (mapcar #'cdr subst)))
	      (push next-goal .next-goals.)
	      (setf (rule-lhs next-target) (substitution-image-simplifying subst (rule-lhs next-target))
		    (rule-rhs next-target) (substitution-image-simplifying subst (rule-rhs next-target))
		    (rule-condition next-target) (if (is-true? (rule-condition next-target))
						     *bool-true*
						   (substitution-image-simplifying subst (rule-condition next-target))))
	      (compute-rule-method next-target)
	      (setf (goal-targets next-goal) (list next-target))
	      (dolist (op new-ops)
		(push op (goal-constants next-goal))))))))
    (if .next-goals.
	(values t (nreverse .next-goals.))
      (values nil nil))))

;;; ===================================
;;; TACTIC: Simultaneous Induction [SI]
;;; ===================================

(defun set-indvars (ptree-node variables)
  (declare (type ptree-node ptree-node))
  (let* ((cur-goal (ptree-node-goal ptree-node))
	 (cur-targets (goal-targets cur-goal))
	 (ind-vars nil))
    (dolist (cur-target cur-targets)
      (let ((target-variables (axiom-variables cur-target)))
	(dolist (v variables)
	  (let ((tv (find-if #'(lambda (x) (and (eq (variable-name v) (variable-name x))
						(eq (variable-sort v) (variable-sort x))))
			     target-variables)))
	    (if tv (pushnew v ind-vars :test #'equal :key #'(lambda (x) (variable-name x)))
	      (with-output-chaos-error ('no-such-variable)
		(format t "Setting induction variable, no such variable ~a:~a in target axiom." (variable-name v) (variable-sort v))))))))
    (setf (goal-indvars cur-goal) ind-vars)
    (format t "~%** Induction will be conducted on ")
    (dolist (var ind-vars)
      (term-print-with-sort var) (princ " "))
    ind-vars))

(defun gather-constructor-ops (module)
  (let ((res nil))
    (with-in-module (module)
      (dolist (opinfo (module-all-operators *current-module*))
	(dolist (meth (opinfo-methods opinfo))
	  (when (method-is-constructor? meth)
	    (push meth res))))
      res)))

;;;
;;; induction-cases
;;; Note: assumes there properly set induction variables in the current goal.
;;;
(defun get-variable-constructors (v constructors)
  (let ((ops nil))
    (dolist (op constructors)
      (when (sort<= (method-coarity op) (variable-sort v))
	(push op ops)))
    (unless ops
      (with-output-chaos-error ('internal-error)
	(format t "Finding constructor of sort ~s, none was found." (sort-name (variable-sort v)))))
    ops))

(defun get-target-variable (indvar axiom-variables)
  (find-if #'(lambda (m) (and (sort= (variable-sort m) (variable-sort indvar))
			      (equal (variable-name m) (variable-name indvar))))
	   axiom-variables))

(defun set-base-cases (target ind-vars base-goal constructors)
  (let ((base-case-terms nil))
    (dolist (ivar ind-vars)
      (let ((base-ops (remove-if #'(lambda (m) (method-arity m)) (get-variable-constructors ivar constructors))))
	(unless base-ops
	  (with-output-chaos-error ('no-base-case-op)
	    (format t "There is no base case constructor for variable ")
	    (term-print-with-sort ivar)))
	(with-in-module ((goal-context base-goal))
	  (dolist (op base-ops)
	    (let* ((new-target (rule-copy-canonicalized target *current-module*))
		   (ax-vars (axiom-variables new-target))
		   (v nil))
	      ;; setup new target
	      (when (setq v (get-target-variable ivar ax-vars))
		(setf (rule-lhs new-target)
		  (substitution-image-simplifying (acons v (make-applform-simple (method-coarity op) op nil) nil)
						  (rule-lhs new-target))
		  (rule-rhs new-target)
		  (substitution-image-simplifying (acons v (make-applform-simple (method-coarity op) op nil) nil)
						  (rule-rhs new-target))
		  (rule-condition new-target)
		  (substitution-image-simplifying (acons v (make-applform-simple (method-coarity op) op nil) nil)
						  (rule-condition new-target))))
	      (push new-target base-case-terms))))))
    (setf (goal-targets base-goal) (nconc (goal-targets base-goal) base-case-terms))))

(defun make-step-constructor-terms (indvar const-ops)
  )

(defun set-step-cases (target ind-vars step-goal constructors)
  (with-in-module ((goal-context step-goal))
    (let ((i-constant-subst (make-tc-variable-substitutions *proof-tree *current-module* ind-vars))
	  (new-targets nil))
      (flet ((get-variable-induction-constant (var)
	       (assoc var i-constant-subst :test #'(lambda (x) (and (sort= (variable-sort x) (variable-sort v))
								    (equal (variable-name x) (variable-name v)))))))
	(dolist (ivar ind-vars)
	  ;; introduce hypothesis
	  (let* ((hypo (rule-copy-canonicalized target *current-module*))
		 (hvars (axiom-variables hypo))
		 (new-target nil)
		 (v nil))
	    ;; make hypothesis
	    (when (setq v (get-target-variable ivar hvars))
	      (let* ((const (get-variable-induction-constant v))
		     (subst (acons v const nil)))
		(setf (rule-lhs hypo) (substitution-image-simplifying subst (rule-lhs hypo))
		      (rule-rhs hypo) (substitution-image-simplifying subst (rule-rhs hypo))
		      (rule-condition hypo) (if (is-true? (rule-condition next-target))
						*bool-true*
					      (substitution-image-simplifying subst (rule-condition hypo))))
		(compute-rule-method hypo)
		(adjoin-axiom-to-module *current-module* hypo)))
	    ;; 
	    (let ((step-ops (remove-if-not #'(lambda (m) (method-arity m)) (get-variable-constructors ivar constructors))))
	      (when (and step-ops v)
		;; setup new target
		(let* ((cterms (make-step-constructor-terms v step-ops))
		       (new-target (rule-copy-canonicalized target *current-module*))
		       (tvars (axiom-variables new-target))
		       (subst nil))
		  (dolist (cterm cterms)
		    (setq tvars (axiom-variables new-target))
		    (when (setq v (get-target-variable ivar tvars))
		      (setq subst (acons v cterm nil))
		      (setf (rule-lhs new-target) (substitution-image-simplifying subst (rule-lhs new-target))
			    (rule-rhs new-target) (substitution-image-simplifying subst (rule-rhs new-target))
			    (rule-condition new-target) (if (is-true? (rule-condition new-target))
							    *bool-true*
							  (substitution-image-simplifying subst (rule-condition new-target)))))
		    (setq applied t)
		    (push new-target new-targets)))))))
	(unless new-targets (push target new-targets))
	(setf (goal-targets step-goal) (nconc (goal-targets step-goal) (nreverse new-targets)))))))
				

(defun induction-cases (parent-node)
  (declare (type ptree-node parent-node))
  (let* ((cur-goal (ptree-node-goal parent-node))
	 (cur-targets (goal-targets cur-goal))
	 (indvars (goal-indvars cur-goal))
	 (constructors (gather-constructor-ops (goal-context cur-goal)))
	 (base-goal (prepare-next-goal parent-node))
	 (step-goal (prepare-next-goal parent-node)))
    (dolist (target cur-targets)
      (set-base-cases target indvars base-goal constructors)
      (set-step-cases target indvars step-goal constructors))
      ;; prepare next goals
    (values t (list base-goal step-goal))))

(defun apply-si (ptree-node)
  (declare (type ptree-node ptree-node))
  ;; internally apply-rd
  (apply-rd ptree-node)
  ;;
  (let ((cur-goal (ptree-node-goal ptree-node)))
    (unless (goal-indvars cur-goal) (return-from apply-si nil))
    (unless (goal-targets cur-goal) (return-from apply-si nil))
    (multiple-value-bind (applied new-goals)
	(induction-cases ptree-node)
      (if applied
	  (values applied new-goals)
	(values nil nil)))))

;;; =======================
;;; TACTIC: REDUCTION [RD]
;;; =======================
(defun reduce-sentence (ax)
  (let* ((target (rule-copy-canonicalized ax *current-module*))
	 (lhs (rule-lhs target))
	 (rhs (rule-rhs target))
	 (condition (rule-condition target)))
    (!setup-reduction *current-module*)
    (let ((*perform-on-demand-reduction* t)
	  (*rule-count* 0))
      (rewrite lhs *current-module*)
      (rewrite rhs *current-module*)
      (rewrite condition *current-module*)
      (values (not (= 0 *rule-count*)) target))))

(defun sentence-is-satisfied (sentence)
  (let ((lhs (rule-lhs sentence))
	(rhs (rule-rhs sentence))
	(condition (rule-condition sentence)))
    (and (is-true? condition)
	 (term-equational-equal lhs rhs))))

(defun apply-rd (ptree-node)
  (declare (type ptree-node ptree-node))
  (let* ((cur-goal (ptree-node-goal ptree-node))
	 (cur-targets (goal-targets cur-goal))
	 (reduced-targets nil)
	 (discharged nil)
	 (result nil))
    (with-in-module ((goal-context cur-goal))
      (dolist (target cur-targets)
	(multiple-value-bind (applied sentence)
	    (reduce-sentence target)
	  (when applied (setq result t))
	  (if (sentence-is-satisfied sentence)
	      (push sentence discharged)
	    (push sentence reduced-targets))))
      (setf (goal-targets cur-goal) (nreverse reduced-targets))
      (setf (goal-proved cur-goal) (nreverse discharged))
      ;; (unless reduced-targets (discharge ptree-node))
      (values result nil))))

;;; ==========================
;;; TACTIC: Case Analysis [CA]
;;; ==========================
(defun apply-ca (ptree-node)
  ptree-node)

;;; ======================================
;;; TACTIC: Case Analysis on Sequence [CS]
;;; ======================================
(defun apply-cs (ptree-node)
  ptree-node)

;;; *****************************************************
;;; APPLY-TACTIC
;;; apply-tactic : ptree-node tactic -> List(ptree-node)
;;; returns the list of generated goal nodes.
;;; -----------------------------------------------------

(defun apply-tactic (ptree-node tactic)
  (declare (type ptree-node ptree-node)
	   (type tactic tactic))
  (when (goal-is-discharged (ptree-node-goal ptree-node))
    (with-output-chaos-warning ()
      (format t "The goal ~s has been proved!." (goal-name (ptree-node-goal ptree-node)))
      (return-from apply-tactic nil)))
  ;; 
  (format t "~%** Applying ~a to goal ~s" tactic (goal-name (ptree-node-goal ptree-node)))
  (multiple-value-bind (applied next-goals)
      (funcall (tactic-executor tactic) ptree-node)
    (declare (type (or null t) applied)
	     (type list next-goals))
    (unless applied (return-from apply-tactic nil))
    (unless next-goals
      #||
      ;; this means this goal is successfully proved
      (if (null (discharge-node ptree-node))
	  ;; all over
	  (return-from apply-tactic :done)
	(return-from apply-tactic nil))
      ||#
      (return-from apply-tactic nil))
    (format t "~%** Generated ~d goal~p" (length next-goals) (length next-goals))
    (format t "~%-- generated goal~p --" (length next-goals))
    (dolist (goal next-goals)
      (pr-goal goal)
      (add-ptree-child ptree-node goal))
    (ptree-node-subnodes ptree-node)))

(defun check-success (ptree)
  (when (get-unproved-goals ptree)
    (return-from check-success nil))
  (format t "~%** All goals are successfully discharged.")
  t)

;;;
;;; apply-tactics 
;;;
(defun apply-tactics (ptree tactics)
  (let ((*apply-in-automatic* (> (length tactics) 1))
	(target-nodes (get-unproved-nodes ptree)))
    (unless target-nodes
      (format t "~%** All goals have been proved!")
      (return-from apply-tactics nil))
    (dolist (tactic tactics)
      (if *apply-in-automatic*
	  (dolist (target-node (get-unproved-nodes ptree))
	    (apply-tactic target-node tactic))
	(apply-tactic (car (get-unproved-nodes ptree)) tactic)))
    (check-success ptree)))

;;;
;;; apply-tactic-to-goal
;;;
(defun apply-tactic-to-goal (ptree name tactic)
  (let ((target-node (find-goal-node ptree name)))
    (unless target-node
      (with-output-chaos-error ('no-named-goal)
	(format t "There is no goal with name ~s." name)))
    (apply-tactic target-node tactic)
    (check-success ptree)))

;;; EOF
