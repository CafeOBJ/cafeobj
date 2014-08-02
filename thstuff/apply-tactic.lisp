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

(defun intro-const-returns-subst (module name variable)
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
			  
(defun make-tc-const-name (ptree prefix)
  (format nil "~a#C~d" prefix (incf (ptree-num-gen-const ptree))))

;;; =======================
;;; TACTIC: IMPLICATION[IP]
;;; =======================
(defun apply-ip (ptree-node)
  (declare (type ptree-node ptree-node))
  ;; normalize
  (apply-rd ptree-node)
  ;;
  (with-in-context (ptree-node)
    (dolist (target .cur-targets.)
      (let ((cond (rule-condition target)))
	(unless (or (is-true? cond) (term-variables cond))
	  (let ((next-goal (prepare-next-goal ptree-node .tactic-ip.)))
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

(defun make-tc-variable-substitutions (ptree module vars)
  (declare (type ptree ptree)
	   (module module)
	   (list vars))
  (let ((subst nil))
    (dolist (var vars)
      (push (intro-const-returns-subst module (make-tc-const-name ptree "tc") var)
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
	(let ((next-goal (prepare-next-goal ptree-node .tactic-tc.)))
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

;;; set-indvars : ptree-node List(variable) -> List(variable)
;;; handler of ':ind on' command
;;;
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
    (format t "~%>> Induction will be conducted on ")
    (dolist (var ind-vars)
      (term-print-with-sort var) (princ " "))
    ind-vars))

;;;
;;; gather-constructor-ops : module -> List(constructor)
;;; list up all the constructor ops in a given module
;;;
(defun gather-constructor-ops (module)
  (let ((res nil))
    (with-in-module (module)
      (dolist (opinfo (module-all-operators *current-module*))
	(dolist (meth (opinfo-methods opinfo))
	  (when (method-is-constructor? meth)
	    (push meth res))))
      res)))

;;;
;;; get-induction-variable-constructors : variable -> List(constructor)
;;; returns a list of constructors of a given induction variable
;;;
(defun get-induction-variable-constructors (v constructors)
  (let ((ops nil))
    (dolist (op constructors)
      (when (sort<= (method-coarity op) (variable-sort v) (module-sort-order *current-module*))
	(push op ops)))
    (unless ops
      (with-output-chaos-error ('internal-error)
	(format t "Finding constructor of sort ~s, none was found." (sort-name (variable-sort v)))))
    ;; we sort the list of ops by number of arguments
    ;; this is important for generating step cases.
    (sort ops #'(lambda (x y) (< (length (method-arity x)) (length (method-arity y)))))))

;;;
;;; get-indvar-constructors
;;; returns a list of (indvar . const1 const2 ...constn) for an induction variable indvar.
;;;
(defun get-indvar-constructors (indvars constructors)
  (let ((ivar-map nil))
    (dolist (iv indvars)
      (push (cons iv (get-induction-variable-constructors iv constructors)) ivar-map))
    (nreverse ivar-map)))

;;;
;;; make-indvar-comb-substitutions : List(variable) List(constructor) -> List(substitution)
;;; returns all possible substitution patterns of induction variables.
;;; ex. for induction variables A, B, C, there are constructors 
;;;     op a-1 : -> A . op a-2 : ->  A
;;;     op b-1 : B -> B
;;;     op c-1 : -> C . op c-2 : -> C . op c-3 : C -> C
;;; this will proces the following substitutions:
;;; (((A . A-1) (B . B-1) (C . C-1))
;;;  ((A . A-2) (B . B-1) (C . C-2))
;;;  ((A . A-1) (B . B-1) (C . C-3))
;;;  ((A . A-2) (B . B-1) (C . C-1))
;;;  ((A . A-1) (B . B-1) (C . C-2))
;;;  ((A . A-2) (B . B-1) (C . C-3)))
;;;
(defun make-indvar-comb-substitutions (indvars constructors)
  (let ((alist (get-indvar-constructors indvars constructors)))
    (make-alist-combinations alist)))

(defun make-alist-combinations (alist)
  (let ((len (reduce #'* (mapcar #'(lambda (x) (length (cdr x))) alist))))
    (declare (fixnum len))
    (let ((result (make-array len))
	  (all-subst nil))
      (dolist (al alist)
	(let* ((elist (cdr al))
	       (l (length elist)))
	  (loop (when (> l len) (return))
	    (setq elist (append elist elist))
	    (incf l))
	  (dotimes (x len)
	    (push (cons (car al) (nth x elist)) (aref result x)))))
      (dotimes (x len)
	(push (nreverse (aref result x)) all-subst))
      (nreverse all-subst))))

;;;
;;; get-induction-base-substitutions : List(substitution) -> List(substitution)
;;;
(defun get-induction-base-substitutions (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (when (every #'(lambda (sub) (null (method-arity (cdr sub)))) subst)
	(push subst res)))
    (nreverse res)))

;;;
;;; get-induction-step-substitutions : List(substitution) -> List(substitution)
;;;
(defun get-induction-step-substitutions (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (unless (every #'(lambda (sub) (null (method-arity (cdr sub)))) subst)
	(push subst res)))
    (nreverse res)))

;;;
;;; get-induction-target-variable : variable List(variable) -> { variable | null }
;;; finds an induction variable from a list.
;;;
(defun get-induction-target-variable (indvar axiom-variables)
  (find-if #'(lambda (m) (and (sort= (variable-sort m) (variable-sort indvar))
			      (equal (variable-name m) (variable-name indvar))))
	   axiom-variables))

;;;
;;; make-real-induction-subst
;;;
(defun make-real-induction-subst (subst axiom-vars)
  (let ((rsubst nil))
    (dolist (sub subst)
      (let ((iv (car sub))
	    (op (cdr sub))
	    (rv nil))
	(when (setq rv (get-induction-target-variable iv axiom-vars))
	  (setq rsubst (acons rv (make-applform-simple (method-coarity op) op nil) rsubst)))))
    rsubst))

;;;
;;; set-base-cases
;;; generates base case axioms for a given target 
;;;
(defun set-base-cases (goal target base-substitutions)
  (let ((all-targets nil))
    (with-in-module ((goal-context goal))
      (dolist (subst base-substitutions)
	(let* ((new-target (rule-copy-canonicalized target *current-module*))
	       (real-subst (make-real-induction-subst subst (axiom-variables new-target))))
	  (setf (rule-lhs new-target) (substitution-image-simplifying real-subst (rule-lhs new-target))
		(rule-rhs new-target) (substitution-image-simplifying real-subst (rule-rhs new-target))
		(rule-condition new-target) (substitution-image-simplifying real-subst (rule-condition new-target)))
	  (push new-target all-targets)))
      (setf (goal-targets goal) (nconc (goal-targets goal) all-targets)))))


(defun make-ind-variable-substitution (ptree module var)
  (declare (type ptree ptree)
	   (module module))
  (intro-const-returns-subst module (make-tc-const-name ptree "si") var))

(defun make-step-constructor-term (goal op one-arg)
  (with-in-module ((goal-context goal))
    (let ((arity (method-arity op))
	  (arg-list nil))
      (dolist (s arity)
	(cond ((sort<= (term-sort one-arg) s *current-sort-order*)
	       (push one-arg arg-list)
	       (setq one-arg (make-variable-term *cosmos* 'dummy)))
	      (t (multiple-value-bind (op meth)
		     (declare-operator-in-module (list (format nil "X#C~d" (incf (ptree-num-gen-const *proof-tree*))))
						 nil
						 s
						 *current-module*
						 nil ; constructor?
						 nil ; behavioural?
						 nil ; not coherent
						 )
		   (declare (ignore op))
		   (let ((const (make-applform-simple s meth nil)))
		     (push const arg-list)
		     (push const (goal-constants goal)))))))
      (when *debug-citp*
	(format t "~%>>[args] ")
	(dolist (x (reverse arg-list))
	  (term-print-with-sort x)
	  (princ ", ")))
      (prepare-for-parsing *current-module*)
      (let ((res (make-applform-simple (method-coarity op) op (nreverse arg-list))))
	(when *debug-citp*
	  (format t "~%>>[step term] ")
	  (term-print-with-sort res))
	res))))

;;;
;;; make-induction-step-subst : goal axiom List((var . op)) -> substitution
;;; 
(defun make-induction-step-subst (goal target v-op-list)
  (let ((h-subst nil)
	(axiom-vars (axiom-variables target)))
    (when *debug-citp*
      (format t "~%>>[mriss] ")
      (print-substitution v-op-list))
    (dolist (sub v-op-list)
      (let* ((iv (car sub))		; induction variable
	     (op (cdr sub))		; operator
	     (rv nil))			; real induction variable in target
	(when (setq rv (get-induction-target-variable iv axiom-vars))
	  (cond ((null (method-arity op))
		 ;; operator is constant
		 (push (cons iv (make-applform-simple (method-coarity op) op nil)) h-subst))
		(t (let* ((c-sub (make-ind-variable-substitution *proof-tree* *current-module* rv))
			  (const-term (cdr c-sub)))
		     (push const-term (goal-constants goal))
		     (push (cons rv (list const-term (make-step-constructor-term goal op (cdr c-sub)))) h-subst)))))))
    ;; make all possible combinations
    (make-alist-combinations h-subst)))

(defun get-hypothesis-subst (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (unless (every #'(lambda (sub) (term-subterms (cdr sub))) subst)
	(push subst res)))
    (nreverse res)))

(defun get-step-subst (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (when (every #'(lambda (sub) (term-subterms (cdr sub))) subst)
	(push subst res)))
    (nreverse res)))

;;;
;;; add-hypothesis
;;; Note: assumes computing module context is established.
;;;
(defun add-hypothesis (step-goal target is-subst)
  (let ((hypo-subst (get-hypothesis-subst is-subst)))
    (dolist (sub hypo-subst)
      (let* ((hypo (rule-copy-canonicalized target *current-module*))
	     (subst (make-real-induction-step-subst sub (axiom-variables hypo))))
	(when *debug-citp*
	  (format t "~%>>[applying hypo subst] ")
	  (print-substitution subst))
	(setf (rule-lhs hypo) (substitution-image-simplifying subst (rule-lhs hypo))
	      (rule-rhs hypo) (substitution-image-simplifying subst (rule-rhs hypo))
	      (rule-condition hypo) (if (is-true? (rule-condition hypo))
					*bool-true*
				      (substitution-image-simplifying subst (rule-condition hypo))))
	(compute-rule-method hypo)
	(adjoin-axiom-to-module *current-module* hypo)
	(setf (goal-assumptions step-goal) (nconc (goal-assumptions step-goal) (list hypo)))))))

(defun make-real-induction-step-subst (subst variables)
  (let ((rsubst nil))
    (when *debug-citp*
      (format t "~%>>[mriss] ")
      (print-substitution subst))
    (dolist (sub subst)
      (let ((iv (car sub))
	    (term (cdr sub))
	    (rv nil))
	(when (setq rv (get-induction-target-variable iv variables))
	  (setq rsubst (acons rv term rsubst)))))
    (when *debug-citp*
      (format t "~%>>r[mriss] ")
      (print-substitution rsubst))
    rsubst))

;;;
;;; add-step-cases
;;; Note: assumes computing module context is established.
;;;
(defun add-step-cases (step-goal target is-subst)
  (let ((step-subst (get-step-subst is-subst)))
    (dolist (sub step-subst)
      (let* ((new-target (rule-copy-canonicalized target *current-module*))
	     (subst (make-real-induction-step-subst sub (axiom-variables new-target))))
	(when (car subst)
	  (when *debug-citp*
	    (format t "~%>>[applying step subst] ")
	    (print-substitution subst))
	  (setf (rule-lhs new-target) (substitution-image-simplifying subst (rule-lhs new-target))
		(rule-rhs new-target) (substitution-image-simplifying subst (rule-rhs new-target))
		(rule-condition new-target) (if (is-true? (rule-condition new-target))
						*bool-true*
					      (substitution-image-simplifying subst (rule-condition new-target))))
	  (setf (goal-targets step-goal) (nconc (goal-targets step-goal) (list new-target))))))))
				
;;;
;;; induction-cases
;;; Note: assumes there properly set induction variables in the current goal.
;;;
(defun induction-cases (parent-node)
  (declare (type ptree-node parent-node))
  (let* ((cur-goal (ptree-node-goal parent-node))
	 (cur-targets (goal-targets cur-goal))
	 (indvars (goal-indvars cur-goal))
	 (all-subst (make-indvar-comb-substitutions indvars
						    (gather-constructor-ops (goal-context cur-goal))))
	 (base-goal (prepare-next-goal parent-node .tactic-si.))
	 (step-goals nil))
    ;;
    ;; generate base cases
    ;;
    (dolist (target cur-targets)
      (set-base-cases base-goal target (get-induction-base-substitutions all-subst)))
    
    ;; generate step cases
    ;; we generate all possible combinations of given induction variables.
    ;; for each combination, we construct a new goal.
    (dolist (subst (get-induction-step-substitutions all-subst))
      (let ((step-goal (prepare-next-goal parent-node .tactic-si.)))
	(with-in-module ((goal-context step-goal))
	  ;; following functions and their callies can assume the computing context is established.
	  (dolist (target cur-targets)
	    (let ((is-subst (make-induction-step-subst step-goal target subst)))
	      (add-hypothesis step-goal target is-subst)
	      (add-step-cases step-goal target is-subst)))
	  (!setup-reduction (goal-context step-goal))
	  (push step-goal step-goals))))
    ;; 
    (values t (cons base-goal (nreverse step-goals)))))

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
  (let ((*chaos-quiet* t))
    (when (goal-is-discharged (ptree-node-goal ptree-node))
      (with-output-chaos-warning ()
	(format t ">> The goal ~s has been proved!." (goal-name (ptree-node-goal ptree-node)))
	(return-from apply-tactic nil)))
    ;; 
    (format t "~%>> Applying ~a to goal ~s" tactic (goal-name (ptree-node-goal ptree-node)))
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
      (format t "~%>> Generated ~d goal~p" (length next-goals) (length next-goals))
      (dolist (goal next-goals)
	(pr-goal goal)
	(add-ptree-child ptree-node goal))
      (ptree-node-subnodes ptree-node))))

(defun check-success (ptree)
  (let ((unp (get-unproved-goals ptree)))
    (when unp
      (format t "~%>> Next target goal is ~s" (goal-name (car unp)))
      (return-from check-success nil))
    (format t "~%>> All goals are successfully discharged.")
    t))

;;;
;;; apply-tactics 
;;;
(defun apply-tactics (ptree tactics)
  (let ((*apply-in-automatic* (> (length tactics) 1))
	(target-nodes (get-unproved-nodes ptree)))
    (unless target-nodes
      (format t "~%>> All goals have been proved!")
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
