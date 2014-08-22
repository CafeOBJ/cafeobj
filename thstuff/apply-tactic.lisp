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

;;; *****************************************************************************
;;; UTILITIES
;;; ****************************************************************************

;;; distribute-sentences : ptree-node List(axiom) -> List(goal)
;;; if there are multiple sentences, distribute them into newly genereted goals for each
;;;
(defun distribute-sentences (parent axioms tactic)
  (declare (type ptree-node parent))
  (let ((new-goals nil)
	(goal nil))
    (cond ((cdr axioms)
	   (dolist (ax axioms)
	     (setq goal (prepare-next-goal parent tactic))
	     (setf (goal-targets goal) (list ax))
	     (push goal new-goals)))
	  (t (push (ptree-node-goal parent) new-goals)))
    (nreverse new-goals)))

;;; rule-copy-cononicalized : rule module -> rule
;;; copy rule with all variables are renewed and noralized.
;;;
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
;;; apply-substitution-to-axiom : subst axiom [label] [add] -> axiom'
;;;
(defun apply-substitution-to-axiom (subst axiom &optional label add)
  (setf (rule-lhs axiom) (substitution-image-simplifying subst (rule-lhs axiom))
	(rule-rhs axiom) (substitution-image-simplifying subst (rule-rhs axiom))
	(rule-condition axiom) (if (is-true? (rule-condition axiom))
				   *bool-true*
				 (substitution-image-simplifying subst (rule-condition axiom))))
  (when label
    (if add
	(setf (rule-labels axiom) (append (if (atom label)
					      (list label)
					    label)
					  (rule-labels axiom)))
      (setf (rule-labels axiom) label)))
  axiom)

;;;
;;; copy-constant-term
;;;
(defun copy-constant-term (constant)
  (make-applform-simple (term-sort constant) (term-head constant) nil))

;;;
;;; select-comb-elems : List(List) -> List
;;; 
(defun select-combs-aux (max-idx list-of-list)
  (declare (type fixnum max-idx)
	   (type list list-of-list))
  (let* ((result nil)
	 (target (car list-of-list))
	 (rest (cdr list-of-list))
	 (len (length target)))
    (declare (type fixnum len)
	     (type list result target rest))
    (if target
	(let ((idx 0))
	  (declare (type fixnum idx))
	  (while (< idx max-idx)
	    (let ((elt (nth (mod idx len) target))
 		  (rr (select-combs-aux max-idx rest)))
 	      ;; (format t "~%:idx=~d :elt=~s :rr=~s" idx elt rr)
	      (if rr
		  (dolist (r rr)
		    (pushnew (cons elt r) result :test #'equal))
		(pushnew (list elt) result :test #'equal))
	      (incf idx)))
	  (nreverse result))
      nil)))

(defun select-comb-elems (list-of-list)
  (declare (type list list-of-list))
  (unless list-of-list (return-from select-comb-elems nil))
  (let ((max-idx ;; (reduce #'* (mapcar #'(lambda (x) (length x)) list-of-list))
	 (apply #'max (mapcar #'(lambda (x) (length x)) list-of-list))))
    (declare (type fixnum max-idx))
    (select-combs-aux max-idx list-of-list)))

;;;
;;; axiom-variables : axiom -> List(variable)
;;; returns a list of variables contained in the given axiom
;;;
(defun axiom-variables (ax)
  (let ((lhs (axiom-lhs ax))
	(rhs (axiom-rhs ax))
	(cond (axiom-condition ax))
	(result nil))
    (declare (type list result))
    (setq result (append (term-variables lhs)
			 (append (term-variables rhs)
				 (term-variables cond))))
    (delete-duplicates result :test #'variable-equal)))

;;;
;;; normalize-term-in : module term -> term Bool
;;; reduces the ground terms in given term by rewriting.
;;; if rewritten, returned term is distructively changed.
;;;
(defun normalize-term-in (module term &optional (reduction-mode :red))
  (let ((applied? nil)
	(targets nil))
    (if (term-variables term)
	(setq targets (get-gterms term))
      (setq targets (list term)))
    (if targets
	(with-in-module (module)
	  (dolist (gt targets)
	    (block next
	      (when (term-is-reduced? gt) 
		(return-from next nil))
	      (setq $$matches 0)
	      (let ((*perform-on-demand-reduction* t)
		    (*rewrite-exec-mode* (eq reduction-mode :exec))
		    (*rule-count* 0))
		(rewrite gt *current-module* reduction-mode)
		(unless (= 0 *rule-count*)
		  (setq applied? t)))))
	  (values term applied?))
      (values term nil))))

;;;
;;; normalize-sentence : axiom module -> axiom' Bool
;;; normalize an axiom by reduction, returns the result.
;;; NOTE: given axiom is preserved (not changed).
;;;
(defun normalize-sentence (ax module)
  (with-in-module (module)
    (let* ((target (rule-copy-canonicalized ax module))
	   (lhs (rule-lhs target))
	   (rhs (rule-rhs target))
	   (condition (rule-condition target))
	   (reduction-mode (if (eq (rule-type ax) :equation)
			       :red
			     :exec))
	   (applied nil)
	   (app? nil))
      (flet ((set-applied (val)
	       (or app? (setq app? val))))
	(with-citp-debug ()
	  (with-in-module (module)
	    (format t "~%[NF] target:")
	    (print-next)
	    (print-axiom-brief target)))
	;; normalize lhs
	(multiple-value-setq (lhs applied)
	  (normalize-term-in module (reset-reduced-flag lhs) :red))
	(set-applied applied)
	(when (eq reduction-mode :exec)
	  (multiple-value-setq (lhs applied) (normalize-term-in module (reset-reduced-flag lhs) :exec))
	  (set-applied applied))
	;; normalize rhs
	(multiple-value-setq (rhs applied) (normalize-term-in module (reset-reduced-flag rhs)))
	(set-applied applied)
	;; normalize condition
	(unless (is-true? condition)
	  (multiple-value-setq (condition applied)
	    (normalize-term-in module (reset-reduced-flag condition) :red))
	  (set-applied  applied))
	(setf (rule-lhs target) lhs)
	(setf (rule-rhs target) rhs)
	(setf (rule-condition target) condition)
	;; 
	(with-citp-debug ()
	    (if (not app?)
		(progn (format t "~%    ...not applied: ")
		       (print-axiom-brief target))
	      (progn
		(print-next)
		(princ "==> ") (print-axiom-brief target))))
	  ;;
	(values target app?)))))

;;;
;;; is-contradiction : term term -> Bool
;;; returns true if true ~ false, or false ~ true
;;;
(defun is-contradiction (t1 t2)
  (or (and (is-true? t1) (is-false? t2))
      (and (is-false? t1) (is-true? t2))))

;;;
;;; sentence-is-satisfied : axiom module -> { :satisfied | :ct | nil }
;;;
(defun sentence-is-satisfied (sentence module)
  (let ((old-condition (rule-condition sentence)))
    (multiple-value-bind (norm-sen app?)
	(normalize-sentence sentence module)
      (declare (ignore app?))
      (let ((lhs (rule-lhs norm-sen))
	    (rhs (rule-rhs norm-sen))
	    (condition (rule-condition norm-sen))
	    (result nil))
	(with-citp-debug ()
	  (format t "~%** satisfied?: ")
	  (print-axiom-brief norm-sen))
	(cond ((and (not (is-true? old-condition)) (is-true? condition))
	       (if (is-contradiction lhs rhs)
		   (setq result :ct)
		 (setq result :st)))
	      ((is-true? condition)	; originally the axiom was non-conditional
	       (if (is-contradiction lhs rhs)
		   (setq result :ct)
		 (let ((x-lhs (normalize-term-in module (reset-reduced-flag lhs)))
		       (x-rhs (normalize-term-in module (reset-reduced-flag rhs))))
		   (when (term-equational-equal x-lhs x-rhs)
		     (setq result :st)))))
	      ((is-false? condition)
	       (setq result :ic))
	      (t (setq result nil)))
	;;
	(with-citp-debug ()
	  (format t "~% --> ~a: " result)
	  (print-next)
	  (print-axiom-brief norm-sen))
	;;
	(values result norm-sen)))))

;;; check-contradiction : module -> Bool
;;; check if 'true => false' or 'false => true' can happen or not
;;;

(defun check-true<=>false (module &optional (report-header nil))
  (with-in-module (module)
    (let ((t-rules (method-rules-with-different-top *bool-true-meth*))
	  (f-rules (method-rules-with-different-top *bool-false-meth*))
	  (ct-rule nil))
      (dolist (rule (append t-rules f-rules))
	(with-citp-debug ()
	  (format t "~%check true<=> false")
	  (print-next)
	  (print-axiom-brief rule))
	(when (or (is-true? (rule-condition rule))
		  (is-true? (normalize-term-in module
					       (reset-reduced-flag (term-copy-and-returns-list-variables
								    (rule-condition rule))))))
	  (setq ct-rule rule)
	  (with-citp-debug ()
	    (format t "~% CT found!"))
	  (return nil)))
      (when (and ct-rule report-header)
	(format t "~%[~a] contradiction: " report-header)
	(let ((*print-indent* (+ 2 *print-indent*)))
	  (print-next)
	  (print-axiom-brief ct-rule)))
      ct-rule)))

(defun check-contradiction (module &optional (report-header nil))
  (or (check-true<=>false module report-header)
      (with-in-module (module)
	(let ((true-term (make-applform-simple *bool-sort* *bool-true-meth* nil))
	      (false-term (make-applform-simple *bool-sort* *bool-false-meth* nil)))
	  (let ((true=false (make-applform-simple *bool-sort* *eql-op* (list true-term false-term))))
	    (multiple-value-bind (t-result t-applied?)
		(normalize-term-in module true=false)
	      (when (and t-applied? (is-true? t-result))
		(when report-header
		  (format t "~%[~a] contradiction: " report-header)
		  (print-next)
		  (format t "  `true = false' can be derived!"))
		(return-from check-contradiction t))))))
      nil))

;;;
;;; make-new-assumption : module term [label] -> axiom
;;;
(defun make-new-assumption (module lhs &optional (label-prefix nil))
  (with-in-module (module)
    (let ((r-lhs lhs)
	  (r-rhs *bool-true*)
	  (type :equation))
      (when (method= *eql-op* (term-method lhs))
	;; (T1 = T2) = true  ==> T1 = T2
	(setf r-lhs (term-arg-1 lhs)
	      r-rhs (term-arg-2 lhs)))
      (when (method= *bool-match* (term-method lhs))
	;; (T1 := T2) = true  ==> T2 = T1
	(setf r-lhs (term-arg-2 lhs)
	      r-rhs (term-arg-1 lhs)))
      (when (method= *rwl-predicate* (term-method lhs))
	;; (T1 => T2) = true ==> T1 => T2
	(setf r-lhs (term-arg-1 lhs)
	      r-rhs (term-arg-2 lhs))
	(setq type :rule))
      (compile-module module)
      (let ((axiom (make-rule :lhs (normalize-term-in module (reset-reduced-flag r-lhs))
			      :rhs (normalize-term-in module (reset-reduced-flag r-rhs))
			      :condition *bool-true*
			      :type type
			      :behavioural nil
			      :labels (if label-prefix (list label-prefix) nil))))
	;; check tautology
	(when (term-equational-equal r-lhs r-rhs)
	  (return-from make-new-assumption nil))
	(with-citp-debug ()
	  (format t "~%** new assumption: ")
	  (print-axiom-brief axiom))
	axiom))))

;;;
;;; condition-axioms : 
;;;
(defun condition->axioms (module condition &optional (rule-label nil))
  (with-in-module (module)
    (let ((axs nil)
	  (cps nil))
      (if (method= *bool-cond-op* (term-head condition))
	  (let ((subs (list-assoc-subterms condition *bool-cond-op*)))
	    (dolist (sub subs)
	      (push (term-copy-and-returns-list-variables sub) cps)))
	(setq cps (list (term-copy-and-returns-list-variables condition))))
      (dolist (c cps)
	(let ((new-ax (make-new-assumption module c rule-label)))
	  (when new-ax
	    (compute-rule-method new-ax)
	    (pushnew new-ax axs :test #'rule-is-similar?))))
      (with-citp-debug ()
	(format t "~%[~a] generated axioms:" rule-label)
	(dolist (ax axs)
	  (print-next)
	  (print-axiom-brief ax)))
      axs)))

(defparameter .ct-trial-context-module. (%module-decl* "ct-trial-dummy" :object :user nil))

(defun axiom-is-an-instance-of (ax cx module)
  (with-in-module (module)
    (with-citp-debug ()
      (print-next)
      (format t "* ax: ") (print-axiom-brief ax)
      (print-next)
      (format t "* cx: ") (print-axiom-brief cx))
    (multiple-value-bind (gs subst no-match E-equal)
	(funcall (rule-first-match-method cx) (rule-lhs cx) (rule-lhs ax))
      (when no-match (return-from axiom-is-an-instance-of nil))
      (when e-equal (setq subst nil))
      (let ((pat-instance (substitution-image-simplifying subst (rule-rhs cx)))
	    (t-instance (rule-rhs ax))
	    (next-match-method nil))
	(with-citp-debug ()
	  (format t "~%* matched: ")
	  (print-substitution subst)
	  (print-next)
	  (format t "pat: ") (term-print-with-sort pat-instance)
	  (print-next)
	  (format t "rhs: ") (term-print-with-sort t-instance))

	(when (term-equational-equal t-instance pat-instance)
	  (return-from axiom-is-an-instance-of t))
	;; try other match
	(setq next-match-method (rule-next-match-method cx))
	(loop
	  (multiple-value-setq (gs subst no-match)
	    (funcall next-match-method gs))
	  (when no-match (return-from axiom-is-an-instance-of nil))
	  (setq pat-instance (substitution-image-simplifying subst (rule-rhs cx)))
	  (when (term-equational-equal t-instance pat-instance)
	    (return-from axiom-is-an-instance-of t))))
      nil)))

(defun check-ct-with-axioms (goal axioms &optional report-header)
    (declare (type goal goal)
	     (type list axioms))
    (with-in-module ((goal-context goal))
      (let ((tf-rules (append (method-rules-with-different-top *bool-true-meth*)
			      (method-rules-with-different-top *bool-false-meth*))))
	;; first do light weight check
	(dolist (rule tf-rules)
	  (when (is-true? (rule-condition rule))
	    ;; already CT
	    (when report-header
	      (format t "~%[~a] found contradiction: " report-header)
	      (print-axiom-brief rule))
	    (return-from check-ct-with-axioms :ct)))
	(dolist (rule tf-rules)
	  (let ((cond-axioms (condition->axioms *current-module* (rule-condition rule))))
	    (let ((remaining cond-axioms))
	      (do* ((cax (car remaining) (car remaining))
		    (axs axioms (cdr axs))
		    (ax (car axs) (car axs)))
		  ((or (null cax) (null axs)))
		(when (axiom-is-an-instance-of ax cax *current-module*)
		  (setq remaining (remove cax remaining))))
	      (unless remaining
		(when report-header
		  (format t "~%[~a] found contradiction: " report-header)
		  (print-axiom-brief rule))
		(return-from check-ct-with-axioms :ct)))))
	nil)))

;;; check-sentence&mark-label : sentence module -> (<result> <normalized-sentence> <origina-sentence>)
;;; 
(defun check-sentence&mark-label (sentence module &optional (report-header nil))
  (with-in-module (module)
    (flet ((make-st-label ()
	     (let ((lbl (or report-header 'st)))
	       (cons lbl (rule-labels sentence))))
	   (make-ct-label ()
	     (let ((lbl (if report-header
			    (intern (format nil "CT-~A" report-header))
			  'ct)))
	       (cons lbl (rule-labels sentence))))
	   (make-ic-label ()
	     (let ((lbl (if report-header
			    (intern (format nil "IC-~A" report-header))
			  'ic)))
	       (cons lbl (rule-labels sentence)))))
      ;;
      (let ((target nil)
	    (res nil))
	(if (check-contradiction module report-header)
	    (setq res :ct)
	  (multiple-value-setq (res target)
	    (sentence-is-satisfied sentence *current-module*)))
	(when res
	  ;; discharged by certain reson
	  (setq sentence (rule-copy-canonicalized sentence *current-module*)))
	(case res
	  (:st (when report-header
		 (format t "~%[~a] discharged: " report-header)
		 (print-axiom-brief sentence))
	       (setf (rule-labels sentence) (make-st-label))
	       (values :st target sentence))
	  (:ct (when report-header
		 (format t "~%[~a] discharged: " report-header)
		 (print-axiom-brief sentence))
	       (setf (rule-labels sentence) (make-ct-label))
	       (values :ct target sentence))
	  (:ic (when report-header
		 (format t "~%[~a] discharged: " report-header)
		 (print-axiom-brief sentence))
	       (setf (rule-labels sentence) (make-ic-label))
	       (values :ic target sentence))
	  (otherwise (values nil target sentence)))))))

;;;
;;; set-operator-rewrite-rule : module axiom -> void
;;;
(defun set-operator-rewrite-rule (module axiom)
  (when (term-is-applform? (rule-lhs axiom))
    (add-rule-to-method axiom (term-head (rule-lhs axiom)) (module-opinfo-table module))))

;;;
;;; check-goal-is-satisfied : goal -> ( <result> <normalized-target> <possibly-marked-target> )
;;;
(defun check-goal-is-satisfied (goal &optional (report-header nil))
  (when (cdr (goal-targets goal))
    (with-output-chaos-error ('invalid-proof-seq)
      (format t "Internal error. more than one target!")))
  (with-in-module ((goal-context goal))
    (let ((target (car (goal-targets goal)))
	  (context (goal-context goal)))
      (multiple-value-bind (result norm-target marked-target)
	  (check-sentence&mark-label target context report-header)
	(cond (result
	       ;; dischared by some reason
	       (setf (goal-targets goal) nil)
	       (setf (goal-proved goal) (list marked-target)))
	      ((and (is-true? (rule-condition target))
		    (eq (rule-type target) :equation))
	       (setf target (rule-copy-canonicalized target context))
	       (setf (rule-lhs target) (make-applform-simple *bool-sort*
							     *eql-op*
							     (list (rule-lhs target)
								   (rule-rhs target)))
		     (rule-rhs target) *bool-true*)
	       (multiple-value-bind (res-2 norm-target-2 marked-target-2)
		   (check-sentence&mark-label target context report-header)
		 (declare (ignore norm-target-2 marked-target-2))
		 (when res-2
		   (setf (goal-targets goal) nil)
		   (setf (goal-proved goal) (list marked-target)))))
	      (t ;; nothing to do
	       ))
	(values result norm-target marked-target)))))
;;;
;;; try-prove-with-axioms : module List(axiom) axiom : -> { :satisfied | :ct | nil }
;;;
(defparameter .trial-context-module. (%module-decl* "trial-dummy" :object :user nil))

(defun try-prove-with-axioms (module axioms target &optional (report-header nil))
  (let ((*chaos-quiet* t))
    (let ((tmodule (eval-ast .trial-context-module.)))
      (import-module tmodule :including module)
      (with-in-module (tmodule)
	(dolist (ax axioms)
	  (adjoin-axiom-to-module tmodule ax)
	  (set-operator-rewrite-rule tmodule ax))
	(compile-module tmodule t)
	;; first we check contradiction
	(if (check-contradiction tmodule report-header)
	    :ct
	  ;; the module is consistent, try
	  (sentence-is-satisfied target tmodule))))))

;;; ****************************************************************************
;;; Tactic executors
;;; ****************************************************************************

;;; ===========
;;; TACTIC: NIL
;;; do nothing
;;; ===========

(defun apply-nil (node)
  (declare (ignore node))
  (with-output-chaos-warning ()
    (format t "~%Tactic [NIL] does nothing."))
  (values nil nil))

(defun apply-nil-internal (node sentences &optional (all-together nil) (tactic .tactic-nil.))
  (declare (type ptree-node node)
	   (type list sentences))
  (let ((goals nil))
    (cond (all-together
	   (let ((ngoal (prepare-next-goal node tactic)))
	     (setf (goal-targets ngoal) sentences)
	     (push ngoal goals)))
	  (t (dolist (sentence sentences)
	       (let ((ngoal (prepare-next-goal node tactic)))
		 (setf (goal-targets ngoal) (list sentence))
		 (push ngoal goals)))))
    (values goals (nreverse goals))))

;;; =======================
;;; TACTIC: IMPLICATION[IP]
;;; =======================

(defun generate-ip-derived-axioms (module axiom)
  (condition->axioms module (axiom-condition axiom) 'ip))

(defun apply-ip (ptree-node)
  (declare (type ptree-node ptree-node))
  (with-in-context (ptree-node)
    (let ((original-goal (ptree-node-goal ptree-node)))
      (flet ((push-next-goal (goal)
	       (unless (eq goal original-goal) (push goal .next-goals.))))
	(let ((target-goals (distribute-sentences ptree-node .cur-targets. .tactic-ip.)))
	  (dolist (.cur-goal. target-goals)
	    (multiple-value-bind (result target otarget)
		(check-goal-is-satisfied .cur-goal. 'ip)
	      (declare (ignore otarget))
	      (if result
		  ;; discharged by some reason
		  (push-next-goal .cur-goal.)
		(cond ((and (not (is-true? (rule-condition target)))
			    (null (term-variables (rule-condition target))))
		       ;; t = t' if C
		       ;; C is a ground term and is not true.
		       ;; try if (SP + { C } |- t = t') or not..
		       ;; if this is satisfied, discharge it.
		       (let ((ngoal (if (eq .cur-goal. original-goal)
					(prepare-next-goal ptree-node .tactic-ip.)
				      .cur-goal.)))
			 (with-in-module ((goal-context ngoal))
			   (let ((new-axs (generate-ip-derived-axioms *current-module* target))
				 (next-target (rule-copy-canonicalized target *current-module*)))
			     ;; make the target
			     (setf (rule-condition next-target) *bool-true*)
			     (setf (goal-targets ngoal) (list next-target))
			     
			     ;; add [ip] axioms 
			     (dolist (ax new-axs)
			       (adjoin-axiom-to-module *current-module* ax)
			       (set-operator-rewrite-rule *current-module* ax))
			     (setf (goal-assumptions ngoal) (append (goal-assumptions ngoal) (reverse new-axs)))
			     ;; compile & check 
			     (compile-module *current-module* t)
			     ;; check if introduced axioms can cause true <=> false:
			     (cond ((check-ct-with-axioms ngoal new-axs 'ip)
				    (let ((dscd (rule-copy-canonicalized target *current-module*)))
				      (setf (goal-targets ngoal) nil)
				      (setf (rule-labels dscd) (list '|CT-ip|))
				      (setf (goal-proved ngoal) (list dscd))))
				   (t   ;; check-goal-is-satisfied do all the neccessary things for us.
				    (check-goal-is-satisfied ngoal 'ip)))
			     (push-next-goal ngoal)))))
		      ((is-true? (rule-condition target))
		       ;; discharged.
		       (push-next-goal .cur-goal.))
		      ;; nothig todo. remain the goal as is
		      (t )))))
	  ;; done for all goals
	  (values .next-goals. (nreverse .next-goals.)))))))

;;; =================================
;;; TACTIC: Theorem of Constants [TC]
;;; =================================

(defun make-tc-variable-substitutions (goal vars)
  (declare (type goal goal)
	   (type list vars))
  (let ((subst nil))
    (dolist (var vars)
      (push (cons var (variable->constant goal var)) subst))
    (with-citp-debug ()
      (format t "~%[tc] variable substitution:")
      (print-next)
      (print-substitution subst))
    subst))

(defun apply-tc (ptree-node)
  (declare (type ptree-node ptree-node))
  ;; 
  (with-in-context (ptree-node)
    (let ((original-goal .cur-goal.))
	(flet ((push-next-goal (goal)
		 (unless (eq goal original-goal) (push goal .next-goals.))))
	  (let ((target-goals (distribute-sentences ptree-node .cur-targets. .tactic-tc.)))
	    (dolist (cgoal target-goals)
	      (multiple-value-bind (res sentence osentence)
		  (check-goal-is-satisfied cgoal 'rd)
		(declare (ignore osentence))
		(cond (res
		       ;; discharged 
		       (push-next-goal cgoal))
		      ((axiom-variables sentence)
		       (when (eq cgoal original-goal)
			 (setq cgoal (prepare-next-goal ptree-node .tactic-tc.)))
		       (push-next-goal cgoal)
		       (with-in-module ((goal-context cgoal))
			 (let* ((next-target (rule-copy-canonicalized sentence *current-module*))
				(vars (axiom-variables next-target))
				(subst (make-tc-variable-substitutions cgoal vars)))
			   (apply-substitution-to-axiom subst next-target '(tc) t)
			   (compute-rule-method next-target)
			   (setf (goal-targets cgoal)
			     (list (normalize-sentence next-target *current-module*))))))
		      (t ))))
	    (values .next-goals. (nreverse .next-goals.)))))))

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
		(format t "Setting induction variable, no such variable ~a:~a in target axiom."
			(variable-name v) (variable-sort v))))))))
    (setf (goal-indvars cur-goal) (nreverse ind-vars))
    (format t "~%>> Induction will be conducted on ")
    (dolist (var (goal-indvars cur-goal))
      (term-print-with-sort var) (princ " "))
    ind-vars))

;;;
;;; set-induction-variables
;;; top level function.
(defun set-induction-variables (variables)
  (declare (type list variables))
  (let ((node (car (get-unproved-nodes *proof-tree*))))
    (unless node
      (with-output-chaos-error ('no-unproved)
	(format t "There is no unproved goals.")))
    (set-indvars node variables)))

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
	(format t "Finding constructor of sort ~a, none was found." (string (sort-name (variable-sort v))))))
    ;; we sort the list of ops by number of arguments
    ;; this is important for generating step cases properly.
    (sort ops #'(lambda (x y) (< (length (method-arity x)) (length (method-arity y)))))))

;;;
;;; get-indvar-constructors
;;; returns a list of (indvar . const1 const2 ...constn) for an induction variable indvar.
;;; (((idvar-1 . const-1) ... (idvar-1 ... const-n))
;;;  ((idvar-2 . const-2) ... (idvar-2 ... const-2-m))
;;;     :
;;;  ((idva-i . const-i)  ... (idvar-i ... const-i-k)))
;;; 
(defun get-indvar-constructors (indvars constructors)
  (let ((ivar-map nil))
    (dolist (iv indvars)
      (push (mapcar #'(lambda (cts) (cons iv cts))
		    (get-induction-variable-constructors iv constructors))
	    ivar-map))
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
  (let ((list-of-alist (get-indvar-constructors indvars constructors)))
    (declare (type list list-of-alist))
    (select-comb-elems list-of-alist)))

;;;
;;; get-induction-base-substitutions : List(substitution) -> List(substitution)
;;;
(defun get-induction-base-substitutions (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (when (every #'(lambda (sub) (null (method-arity (cdr sub)))) subst)
	(push subst res)))
    (with-citp-debug ()
      (format t "~%[si] base case subst")
      (dolist (sub res)
	(print-next)
	(print-substitution sub)))
    (nreverse res)))

;;;
;;; get-induction-step-substitutions : List(substitution) -> List(substitution)
;;;
(defun get-induction-step-substitutions (all-subst)
  (let ((res nil))
    (dolist (subst all-subst)
      (unless (every #'(lambda (sub) (null (method-arity (cdr sub)))) subst)
	(push subst res)))
    (with-citp-debug ()
      (format t "~%[si] get-induction-step-subsutitutions")
      (dolist (sub res)
	(print-next)
	(print-substitution sub)))
    (nreverse res)))

;;;
;;; get-real-target-variable : variable List(variable) -> { variable | null }
;;; finds an variable from a list of variables.
;;;
(defun get-real-target-variable (indvar axiom-variables)
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
	(when (setq rv (get-real-target-variable iv axiom-vars))
	  (setq rsubst (acons rv (make-applform-simple (method-coarity op) op nil) rsubst)))))
    rsubst))

;;;
;;; set-base-cases
;;; generates base case axioms for a given target 
;;;
(defun set-base-cases (goal target base-substitutions)
  (let ((all-targets nil)
	(app? nil))
    (with-in-module ((goal-context goal))
      (dolist (subst base-substitutions)
	(let* ((new-target (rule-copy-canonicalized target *current-module*))
	       (real-subst (make-real-induction-subst subst (axiom-variables new-target))))
	  (when real-subst
	    (setq app? t)
	    (apply-substitution-to-axiom real-subst new-target)
	    (push new-target all-targets)))))
    (setf (goal-targets goal) (nconc (goal-targets goal) all-targets))
    app?))

;;;
;;; make-step-constructor-term
;;;
(defun make-step-constructor-term (goal op one-arg variable)
  (with-in-module ((goal-context goal))
    (let ((arity (method-arity op))
	  (arg-list nil))
      (dolist (s arity)
	(cond ((sort<= (term-sort one-arg) s *current-sort-order*)
	       (push one-arg arg-list)
	       (setq one-arg (make-variable-term *cosmos* 'dummy))) ; make ......
	      (t (let ((constant (variable->constructor goal variable :sort s)))
		   (push constant arg-list)))))
      (let ((res (make-applform-simple (method-coarity op) op (nreverse arg-list))))
	res))))

;;;
;;; make-induction-step-subst : goal axiom (var . op) -> substitution
;;; 
(defun make-induction-step-subst (goal target v-op-list)
  ;; we ignore all mapped operators are constant constructors.
  (when (every #'(lambda (v-op)
		   (let ((op (cdr v-op)))
		     (and (null (method-arity op))
			  (method-is-constructor? op))))
	       v-op-list)
    (return-from make-induction-step-subst nil))
  ;;
  (let ((hypo-v-op nil) 
	(step-v-op nil)
	;; (new-ops nil)
	(axiom-vars (axiom-variables target)))
    ;; we generate the following case for each induction variable v:
    ;; 1) (v . <term of constant constructor>)
    ;; 2) (v . <constant term of non-constant-constructor>)
    ;; 3) (v . <application form of non-constant-constructor>)
    ;;
    (dolist (sub v-op-list)
      (let* ((iv (car sub))   ; induction variable
	     (op (cdr sub))   ; operator
	     (rv nil))        ; real induction variable in target
	(when (setq rv (get-real-target-variable iv axiom-vars))
	  (cond ((null (method-arity op))
		 (let* ((ct (variable->constructor goal rv :op op))
			(c-subst (cons iv ct)))
		   ;; operator is constant constructor
		   (push (list (cons iv (list op ct))) hypo-v-op)
		   (push c-subst step-v-op)))
		(t ;; operator is non-constant constructor
		 (let ((const-term (variable->constructor goal rv)))
		   (push (list (cons rv (list op const-term))) hypo-v-op)
		   (push (cons rv (make-step-constructor-term goal op const-term rv)) step-v-op)))))))
    (values (select-comb-elems (nreverse hypo-v-op))
	    (nreverse step-v-op))))

(defun make-real-induction-step-subst (subst variables)
  (let ((rsubst nil))
    (dolist (sub subst)
      (let ((iv (car sub))
	    (term (cdr sub))
	    (rv nil))
	(when (setq rv (get-real-target-variable iv variables))
	  (setq rsubst (acons rv term rsubst)))))
    (nreverse rsubst)))

(defun resolve-induction-subst (goal hypo-v-op step-subst)
  (declare (ignore goal))
  (flet ((make-proper-alist (sub)
	   (mapcar #'(lambda (s) (cons (car s) (cadr s))) sub)))
    (unless hypo-v-op 
      (with-output-chaos-warning ()
	(format t "No subst given.")
	(return-from resolve-induction-subst nil)))
    (let ((rsubsts (mapcar #'(lambda (sub)
			       (cons (car sub) (list (third sub))))
			   hypo-v-op))
	  (all-subst nil))
      (with-citp-debug ()
	(format t "~%[si] resolve induction step: given")
	(print-next) (format t "hypo-v-op: ~s" hypo-v-op)
	(print-next) (princ "step-subst" )
	(print-substitution step-subst))
      ;; return if there are no possible combinations
      ;; (unless (cdr hypo-v-op)
      ;;   (return-from resolve-induction-subst (list (make-proper-alist rsubsts))))
      ;;
      (with-citp-debug ()
	(format t "~%resolve subst: given")
	(dolist (v-op hypo-v-op)
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (format t "(~a . ~a <- " (variable-name (first v-op)) (car (method-name (second v-op))))
	    (term-print-with-sort (third v-op))
	    (princ ")"))))

      ;; make all possible hypothesis substitutions
      (let ((vop-hash (make-hash-table :test #'eq))
	    (vcombs nil))
	(dolist (v-op hypo-v-op)
	  (let ((v (first v-op))
		(as nil))
	    (unless (setq as (assoc v rsubsts))
	      (with-output-chaos-error ('internal-err)
		(format t "!! cannot find variable subst ~s" (variable-name v))))
	    (setf (gethash v vop-hash) (list as))
	    (let ((st (assoc v step-subst :test #'equal))
		  (hentry (gethash v vop-hash))
		  (new-element nil))
	      (unless st (with-output-chaos-error ('no-step-term)
			   (format t "No step term found for variable ~a" (variable-name v))))
	      (setq new-element (cons v (list (cdr st))))
	      (unless (member new-element hentry :test #'equal)
		(setf (gethash v vop-hash) (append hentry (list new-element)))))))
	(maphash #'(lambda (x vl) (declare (ignore x)) (push vl vcombs)) vop-hash)
	(setq all-subst (select-comb-elems vcombs))
	(with-citp-debug ()
	  (format t "~%resolve subt: all possibilities")
	  (let ((*print-indent* (+ 2 *print-indent*))
		(num 0))
	    (declare (type fixnum num))
	    (dolist (vcom all-subst)
	      (print-next)
	      (format t "=== (#~d) " (incf num))
	      (dolist (rs vcom)
		(format t "~a |-> " (variable-name (car rs)))
		(term-print-with-sort (cadr rs)) (princ " ")))))
	;;
	(mapcar #'make-proper-alist all-subst)))))

;;;
;;; add-hypothesis
;;; Note: assumes computing module context is established.
;;;
(defun subst-is-equal (sub1 sub2)
  (dolist (entry sub1)
    (let ((entry2 (assoc (car entry) sub2 :test #'equal)))
      (unless entry2 (return-from subst-is-equal nil))
      (unless (equal (cdr entry) (cdr entry2))
	(return-from subst-is-equal nil))))
  t)

(defun add-hypothesis (step-goal target hypo-subst step-subst)
  (with-citp-debug ()
    (format t "~%[si] add-hypothesis:")
    (print-next) (princ "-- hypo-subst ")
    (dolist (hp hypo-subst)
      (print-next)
      (print-substitution hp))
    (print-next) (princ "-- step-subst ")
    (print-substitution step-subst))
  (dolist (osub hypo-subst)
    (dolist (sub (resolve-induction-subst step-goal osub step-subst))
      (unless (subst-is-equal sub step-subst)
	(let* ((hypo (rule-copy-canonicalized target *current-module*))
	       (subst (make-real-induction-step-subst sub (axiom-variables hypo))))
	  (with-citp-debug
	      (format t "~%>>[applying hypo subst] ")
	    (print-substitution subst)
	    (print-next)
	    (princ "to ")
	    (print-axiom-brief hypo))
	  (apply-substitution-to-axiom subst hypo '(si) t) 
	  (compute-rule-method hypo)
	  (set-operator-rewrite-rule *current-module* hypo)
	  (adjoin-axiom-to-module *current-module* hypo)
	  (with-citp-debug ()
	    (format t "~%--> ")
	    (print-axiom-brief hypo))
	  (setf (goal-assumptions step-goal) (append (goal-assumptions step-goal) (list hypo))))))))

;;;
;;; add-step-cases
;;; Note: assumes computing module context is established.
;;;
(defun add-step-cases (step-goal target step-subst)
  (let* ((new-target (rule-copy-canonicalized target *current-module*))
	 (subst (make-real-induction-step-subst step-subst (axiom-variables new-target))))
    (when (car subst)
      (with-citp-debug
	(format t "~%>>[applying step subst] ")
	(print-substitution subst))
      (apply-substitution-to-axiom subst new-target)
      (setf (goal-targets step-goal) (nconc (goal-targets step-goal) (list new-target))))))
				
;;;
;;; induction-cases
;;; Note: assumes there properly set induction variables in the current goal.
;;;
(defun induction-cases (parent-node)
  (declare (type ptree-node parent-node))
  (let* ((cur-goal (ptree-node-goal parent-node))
	 (cur-targets nil)
	 (indvars (goal-indvars cur-goal))
	 (all-subst (make-indvar-comb-substitutions indvars
						    (gather-constructor-ops (goal-context cur-goal))))
	 (base-goal (prepare-next-goal parent-node .tactic-si.))
	 (step-goals nil)
	 (need-goal nil)
	 (base-generated nil)
	 (remainings nil))
    ;;
    (with-citp-debug ()
      (format t "~%[si] all possible substitutions")
      (let ((num 0))
	(declare (type fixnum num))
	(dolist (subs all-subst)
	  (format t "~%subst #~d" (incf num))
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (print-substitution subs)))))

    ;; implicit NF application
    (dolist (ct (goal-targets cur-goal))
      (multiple-value-bind (ntarget app?)
	  (normalize-sentence ct (goal-context cur-goal))
	(when app? (setq need-goal t))
	(push ntarget cur-targets)))
    (setq cur-targets (nreverse cur-targets))

    ;; generate base cases
    ;;
    (dolist (target cur-targets)
      (if (not (set-base-cases base-goal target (get-induction-base-substitutions all-subst)))
	  (when need-goal
	    (push target remainings))
	(setq base-generated t)))
    (unless base-generated (setq base-goal nil))
    
    ;; generate step cases
    ;; we generate all possible combinations of given induction variables.
    ;; for each combination, we will construct a new goal.
    ;;
    (dolist (subst (get-induction-step-substitutions all-subst))
      (let ((step-goal (prepare-next-goal parent-node .tactic-si.)))
	(with-in-module ((goal-context step-goal))
	  ;; following functions and their callies can assume the computing context is established.
	  (dolist (target cur-targets)
	    (multiple-value-bind (hypo-subst-list step-subst)
		(make-induction-step-subst step-goal target subst)
	      (add-hypothesis step-goal target hypo-subst-list step-subst)
	      (add-step-cases step-goal target step-subst)))
	  (cond ((goal-targets step-goal)
		 (push step-goal step-goals))
		(t )))))		; do nothig
    ;;
    (when remainings
      (multiple-value-bind (ap? nil-goals)
	  (apply-nil-internal parent-node (reverse remainings) :all-togather .tactic-si.)
	(declare (ignore ap?))
	(dolist (ng nil-goals)
	  (push ng step-goals))))
    ;; 
    (if base-goal
	(values t (cons base-goal (nreverse step-goals)))
      (if step-goals
	  ;; case remainings 
	  (values t step-goals)
	(values nil nil)))))

;;;
;;; apply-si : ptree-node -> (applied? . List(goal))
;;;
(defun apply-si (ptree-node)
  (declare (type ptree-node ptree-node))
  (let ((cur-goal (ptree-node-goal ptree-node)))
    (unless (and (goal-indvars cur-goal) (goal-targets cur-goal))
      (return-from apply-si nil))
    (multiple-value-bind (applied new-goals)
	(induction-cases ptree-node)
      (if applied
	  (values applied new-goals)
	(values nil nil)))))

;;; =======================
;;; TACTIC: REDUCTION [RD]
;;; =======================


(defun apply-rd (ptree-node)
  (declare (type ptree-node ptree-node))
  (let* ((cur-goal (ptree-node-goal ptree-node))
	 (cur-targets (goal-targets cur-goal))
	 (reduced-targets nil)
	 (discharged nil)
	 (result nil))
    (when cur-targets
      (with-in-module ((goal-context cur-goal))
	(compile-module *current-module* t)
	(dolist (target cur-targets)
	  (multiple-value-bind (c-result cur-target original-sentence)
	      (check-sentence&mark-label target *current-module* 'rd)
	    (cond (c-result		; satisfied or contradition
		   (setq result t)
		   (push original-sentence discharged))
		  (t (push cur-target reduced-targets)))))
	(setf (goal-targets cur-goal) (nreverse reduced-targets))
	(setf (goal-proved cur-goal) (nreverse discharged))
	(unless reduced-targets
	  (format t "~%[rd] discharged goal ~s." (goal-name cur-goal)))))
    (values result nil)))

;;; ==========================
;;; TACTIC: Case Analysis [CA]
;;; ==========================

;;;
;;; get-gterms : term -> List(ground-term)
;;;
(defun get-gterms (term)
  (let ((gterms nil))
    (when (term-is-applform? term)
      (unless (term-variables term)
	(push term gterms))
      (dolist (arg (term-subterms term))
	(setq gterms (nconc gterms (get-gterms arg)))))
    gterms))

;;;
;;; get-gterms-from-axiom : axiom -> List(ground-term)
;;; 
(defun get-gterms-from-axiom (axiom)
  (let ((gterms (delete-duplicates (append (get-gterms (axiom-lhs axiom))
					   (get-gterms (axiom-rhs axiom)))
				   :test #'equal)))
    (unless (is-true? (axiom-condition axiom))
      (setq gterms (delete-duplicates (append gterms
					      (get-gterms (axiom-condition axiom)))
				      :test #'equal)))
    gterms))

(defun gsubterm-has-matching-rule (gterm c-rules)
  (dolist (term (delete gterm (get-gterms gterm)))
    (dolist (crule c-rules)
      (multiple-value-bind (gs sub no-match eeq)
	  (@matcher (axiom-lhs crule) term :match)
	(declare (ignore eeq sub gs))
	(unless no-match
	  (with-citp-debug
	      (format t "~%>>[ca] sub has matching rule: ") (print-axiom-brief crule)
	      (print-next)
	      (term-print-with-sort term))
	  (return-from gsubterm-has-matching-rule t)))))
  nil)

;;;
;;; find-gterm-matching-conditionals : term List(conditional-rule) -> List(conditional-rule . subst)
;;; given a ground term in target, returns a list of list of pair:
;;;   (
;;;     ((rule-1 . subst-1) ... (rule-i . subst-i))     <-- group 1
;;;            :
;;;     ((rule-n . subst-n) ... (rule-j . subst-j))     <-- group 2
;;;    )
;;;

;;; rs-tuples : ((rule (subst . condition-instance)) ...)
(defun make-ca-rule-groups (rs-tuples)
  (flet ((find-lhs-overwrapped (rs-tuple)
	     (let ((res nil)
		   (lhs-image (substitution-image-simplifying (second rs-tuple) (rule-lhs (first rs-tuple)))))
	       (dolist (rs rs-tuples)
		 (when (and (not (eq rs-tuple rs))
			    (term-equational-equal lhs-image
						   (substitution-image-simplifying (second rs)
										   (rule-lhs (first rs)))))
		 (push rs res)))
	       res)))
    (let ((groups nil))
      (dolist (rsx rs-tuples)
	(unless (find-if #'(lambda (grp) (member rsx grp)) groups)
	  (let ((grp (find-lhs-overwrapped rsx)))
	    (when grp (push (cons rsx grp) groups)))))
      (with-citp-debug ()
	(format t "~%>>[ca] generated ~d case combination~p" (length groups) (length groups))
	(let ((num 1))
	  (dolist (grp (reverse groups))
	    (print-next)
	    (format t "~%#~d" num)
	    (let ((*print-indent* (+ 2 *print-indent*)))
	      (dolist (rsp grp)
		(print-next)
		(print-axiom-brief (first rsp))
		(print-next)
		(princ "   <== ")
		(print-substitution (second rsp))))
	   (incf num))))
      ;;
      (nreverse groups))))

(defun ca-instantiate-condition (goal condition)
  (let ((vars (term-variables condition))
	(subst nil))
    (cond (vars (dolist (v vars)
		  (push (cons v (variable->constant goal v)) subst))
		(substitution-image-simplifying subst condition))
	  (t condition))))

(defvar .subst-so-far. nil)

#||
(defun find-gterm-matching-conditionals (goal gterm conditional-rules)
  (let ((res nil))
    (dolist (rule conditional-rules)
      (block next
	(unless (is-true? (rule-condition rule))
	  (multiple-value-bind (gs sub no-match eeq)
	      (@matcher (axiom-lhs rule) gterm :match)
	    (declare (ignore eeq))
	    (when no-match (return-from next nil))
	    (when (gsubterm-has-matching-rule gterm conditional-rules)
	      (return-from next nil))
	    ;;
	    (with-citp-debug ()
	      (format t "~%[ca] found rs-pair for ")
	      (term-print-with-sort gterm)
	      (print-next)
	      (print-axiom-brief rule)
	      (print-next)
	      (print-substitution sub))
	    (let ((cond-instance (ca-instantiate-condition goal
							   (substitution-image-simplifying sub (rule-condition rule)))))
	      (push (list rule sub cond-instance) res)
	      (loop 
		(let ((n-subst nil)
		      (n-cond-inst nil))
		  (multiple-value-setq (gs n-subst no-match)
		    (next-match gs))
		  (when no-match (return-from next))
		  (with-citp-debug ()
		    (format t "~%[ca] adding extra."))
		  (setq n-cond-inst (ca-instantiate-condition goal
							      (substitution-image-simplifying n-subst (rule-condition rule))))
		  (unless (term-equational-equal n-cond-inst cond-instance)
		    (push (list rule n-subst n-cond-inst)  res)))))))))
    ;; cases for one gterm
    (let ((gps (make-ca-rule-groups res))
	  (result nil))
      (with-citp-debug ()
	(let ((num-gp (length gps)))
	  (format t "~%[ca] found ~d group of cases" num-gp)
	  (dotimes (x num-gp)
	    (let ((gp (nth x gps)))
	      (print-next)
	      (format t "-- ~d -- " x)
	      (dolist (triple gp)
		(print-next) 
		(term-print-with-sort (third triple)))))))
      ;;
      (dolist (gp gps)
	(let ((res nil))
	  (dolist (triple gp)
	    (let ((condition (third triple)))
	      (unless (member condition .subst-so-far. :test #'term-equational-equal)
		(push condition .subst-so-far.)
		(push condition res))))
	  (when res (push res result))))
      result)))
||#
;;;
;;; find-gterm-matching-conditionals : goal term List(conditional axioms) 
;;;                                    -> List(<subst, axiom, condition>)
;;; returns all possible cases for a given ground term.
;;;
(defun find-gterm-matching-conditionals (goal gterm conditional-rules)
  (let ((res nil))
    (dolist (rule conditional-rules)
      (block next
	(unless (is-true? (rule-condition rule))
	  (multiple-value-bind (gs sub no-match eeq)
	      (@matcher (axiom-lhs rule) gterm :match)
	    (declare (ignore eeq))
	    (when no-match (return-from next nil))
	    (when (gsubterm-has-matching-rule gterm conditional-rules)
	      (return-from next nil))
	    ;;
	    (with-citp-debug ()
	      (format t "~%[ca] found rs-pair for ")
	      (term-print-with-sort gterm)
	      (print-next)
	      (print-axiom-brief rule)
	      (print-next)
	      (print-substitution sub))
	    (let ((cond-instance (ca-instantiate-condition goal
							   (substitution-image-simplifying sub (rule-condition rule)))))
	      (push (list rule sub cond-instance) res)
	      (loop 
		(let ((n-subst nil)
		      (n-cond-inst nil))
		  (multiple-value-setq (gs n-subst no-match)
		    (next-match gs))
		  (when no-match (return-from next))
		  (with-citp-debug ()
		    (format t "~%[ca] adding extra."))
		  (setq n-cond-inst (ca-instantiate-condition goal
							      (substitution-image-simplifying n-subst (rule-condition rule))))
		  (unless (term-equational-equal n-cond-inst cond-instance)
		    (push (list rule n-subst n-cond-inst)  res)))))))))
    ;; 
    (let ((tres nil))
      (dolist (triple res)
	(let ((condition (third triple)))
	  (unless (member condition .subst-so-far. :test #'term-equational-equal)
	    (push condition .subst-so-far.)
	    (push condition tres))))
      tres)))

;;;
;;; generate-case-axioms : goal List(< rule . subst >) -> List(axiom)
;;;
(defvar .new-axs-so-far. nil)

(defun generate-case-axioms (next-goal conditions)
  (with-in-module ((goal-context next-goal))
    (let ((case-axioms nil))
      (dolist (condition conditions)
	(let ((list-lhs nil))
	  (if (method= *bool-cond-op* (term-method condition))
	      (dolist (arg (list-assoc-subterms condition *bool-cond-op*))
		(push arg list-lhs))
	    (setq list-lhs (list condition)))
	  (dolist (condition list-lhs)
	    (let ((axs (make-new-assumption *current-module* condition 'ca)))
	      (when axs
		(unless (member axs .new-axs-so-far. :test #'rule-is-similar?)
		  (push axs .new-axs-so-far.)
		  (compute-rule-method axs)
		  (with-citp-debug ()
		    (format t "~%>>[ca] adding an axiom to module ~s" (get-module-simple-name (goal-context next-goal)))
		    (print-next)
		    (print-axiom-brief axs))
		  (set-operator-rewrite-rule *current-module* axs)
		  (adjoin-axiom-to-module *current-module* axs)
		  (push axs case-axioms))))))) ;------
      (compile-module *current-module*)
      (setf (goal-assumptions next-goal) (append (goal-assumptions next-goal)
						 (nreverse case-axioms))))))
						   
;;;
;;; generate-cases : ptree-node term List(conditional-axiom)
;;;
(defun generate-cases (ptree-node target conditional-rules divide?)
  (declare (type ptree-node ptree-node)
	   (list conditional-rules))
  (multiple-value-bind (norm-target app?)
      (normalize-sentence target (goal-context (ptree-node-goal ptree-node)))
    (when app?
      (setq target norm-target))
    (with-citp-debug ()
      (format t "~%** Case Analysis: target -----------")
      (print-next)
      (print-axiom-brief target))
    ;; then generate possible cases
    (let ((gterms (get-gterms-from-axiom target))
	  (next-goals nil)
	  (remainings nil)
	  (.subst-so-far. nil))
      ;; 
      (let ((g-conditions nil))
	(dolist (gterm gterms)
	  (let ((conds (find-gterm-matching-conditionals (ptree-node-goal ptree-node)
							 gterm
							 conditional-rules)))
	    (when conds
	      (setq g-conditions (nconc g-conditions (list conds))))))
	(setq g-conditions (nreverse g-conditions))
	;; make all combinations and generate cases
	(let ((rv-combs (select-comb-elems g-conditions))
	      (next-goal nil))
	  (with-citp-debug ()
	    (format t "~%>>[ca] gterm conditions: ")
	    (if rv-combs
		(let ((rv-com nil))
		  (dotimes (x (length rv-combs))
		    (setq rv-com (nth x rv-combs))
		    (print-next)
		    (format t "--(~d)--" (1+ x))
		    (dolist (rr rv-com)
		      (print-next)
		      (term-print-with-sort rr))))
	      (format t "NONE.")))
	  (cond (rv-combs
		 (dolist (rv-com rv-combs)
		   (let ((.new-axs-so-far. nil))
		     (setq next-goal (prepare-next-goal ptree-node .tactic-ca.))
		     (setf (goal-targets next-goal) (list target))
		     (generate-case-axioms next-goal rv-com)
		     (push next-goal next-goals))))
		(t (push target remainings)))))
      ;;
      (when remainings
	(when (or next-goals app? divide?)
	  (multiple-value-bind (app? nop-goals)
	      (apply-nil-internal ptree-node (reverse remainings) nil .tactic-ca.)
	    (declare (ignore app?))
	    (dolist(ng nop-goals)
	      (push ng next-goals)))))
      (values next-goals (nreverse next-goals)))))

(defun rule-is-for-case (rule)
  (and (not (is-true? (rule-condition rule)))
       (let ((labels (rule-labels rule)))
	 (dolist (lb labels nil)
	   (let ((lstr (string lb)))
	     (when (and (>= (length lstr) 3)
			(string-equal (subseq lstr 0 3) "CA-"))
	       (return-from rule-is-for-case t)))))))

(defun get-ca-rules (module)
  (remove-if-not #'rule-is-for-case (module-all-rules module)))

(defun apply-ca (ptree-node)
  (declare (type ptree-node ptree-node))
  (with-in-context (ptree-node)
    (with-in-module ((goal-context .cur-goal.))
      (let ((crules (get-ca-rules *current-module*))
	    (divide? (cdr .cur-targets.)))
	(dolist (target .cur-targets.)
	  (multiple-value-bind (applied goals)
	      (generate-cases ptree-node target crules divide?)
	    (declare (ignore applied))
	    (when goals (setq .next-goals. (nconc .next-goals. goals)))))
	(values .next-goals. .next-goals.)))))

;;;
(defun rule-is-case-generated (rule)
  (and (is-true? (rule-condition rule))
       (let ((labels (rule-labels rule)))
	 (dolist (lb labels nil)
	   (let ((lstr (string lb)))
	     (when (and (= 2 (length lstr))
			(string-equal lstr "CA"))
	       (return-from rule-is-case-generated t)))))))

(defun print-case-axioms (node)
  (let ((mod (goal-context (ptree-node-goal node)))
	(cas nil))
    (with-in-module (mod)
      (let ((all-rules (module-all-rules mod)))
	(dolist (rule all-rules)
	  (when (rule-is-case-generated rule)
	    (push rule cas))))
      (when cas
	(format t "~%** [CA] generated axioms in goal ~s" (goal-name (ptree-node-goal node)))
	(let ((*print-indent* (+ 2 *print-indent*)))
	  (dolist (rl cas)
	    (print-next)
	    (print-axiom-brief rl)))))))

(defun all-cases ()
  (unless *proof-tree* 
    (with-output-chaos-error ('no-context)
      (format t "No proof tree!")))
  (dag-wfs (ptree-root *proof-tree*)
	   #'print-case-axioms))

;;; ======================================
;;; TACTIC: Case Analysis on Sequence [CS]
;;; TODO
;;; ======================================
(defun apply-cs (ptree-node)
  ptree-node)

;;; ==========================================
;;; INSTANCIATE (non-executable) axiom (:init)
;;; ==========================================

;;; get-target-axiom : module target-form -> {nil | axiom}
;;; target-form : (<kind> <form>)
;;;
(defun get-target-axiom (module target-form &optional (add-to-module nil))
  (let ((kind (first target-form))
	(ax nil))
    (cond ((eq :label kind) (setq ax (get-rule-labelled module (second target-form))))
	  (t (with-in-module (module)
	       (setq ax (parse-axiom-declaration (parse-module-element-1 (cdr target-form))))
	       (when add-to-module
		 (set-operator-rewrite-rule module ax)
		 (adjoin-axiom-to-module module ax)
		 (set-needs-rule)))))
    ax))

;;; resolve-subst-form
;;;
(defun resolve-subst-form (context subst-forms)
  (with-in-module (context)
    (let ((subst nil))
      (dolist (subst-form subst-forms)
	(let ((var-form (first subst-form))
	      (term-form (second subst-form))
	      (var nil)
	      (term nil))
	  (with-citp-debug ()
	    (format t "~%resolving subst form:")
	    (print-next)
	    (format t " var=~s, term=~s" var-form term-form))
	  (setq var (simple-parse-from-string var-form))
	  (when (or (term-ill-defined var) (not (term-is-variable? var)))
	    (with-output-chaos-error ('invalid-var-form)
	      (format t "Invalid variable in substitution: ~s" var-form)))
	  (setq term (simple-parse-from-string term-form))
 	  (when (term-ill-defined term)
	    (with-output-chaos-error ('invalid-term)
	      (format t "No parse..: ~s" term-form)))
	  (unless (sort<= (term-sort term) (variable-sort var) *current-sort-order*)
	    (with-output-chaos-error ('sort-mismatch)
	      (format t "Sort mismatch for the substitution")
	      (print-next)
	      (format t "  variable: ") (term-print-with-sort var)
	      (print-next)
	      (format t "  term: ") (term-print-with-sort term)))
	  (push (cons var term) subst)))
      subst)))

;;; 
(defun make-real-instanciation-subst (subst axiom-vars)
  (let ((rsubst nil)
	rv)
    (dolist (vt-pair subst)
      (if (setq rv (get-real-target-variable (car vt-pair) axiom-vars))
	  (setq rsubst (acons rv (cdr vt-pair) rsubst))
	(with-output-chaos-error ('no-var)
	  (format t "Instanciating an axiom, no such variable ")
	  (term-print-with-sort (car vt-pair)))))
    rsubst))

;;; make-axiom-instance : module substitution axiom -> axiom'
;;; terms in resulting axiom must be ground terms.
;;;
(defun make-axiom-instance (module subst axiom)
  (let ((new-axiom (rule-copy-canonicalized axiom module))
	(rsubst nil))
    (setq rsubst (make-real-instanciation-subst subst (axiom-variables new-axiom)))
    (apply-substitution-to-axiom rsubst new-axiom '(init))
    #||
    (when (axiom-variables new-axiom)
      (with-output-chaos-error ('not-ground)
	(format t "Instanciating an axiom, not all variable substitutions are supplied.")
	(dolist (v (axiom-variables new-axiom))
	  (print-next)
	  (term-print-with-sort v))))
    ||#
    new-axiom))

;;;
;;; instanciate-axiom
;;; 
(defun instanciate-axiom (target-form subst-form)
  (let ((context (get-next-proof-context *proof-tree*)))
    (unless context
      (with-output-chaos-error ('no-context)
	(format t "Instanciating axiom, no context module is established.")))
    (with-in-module ((goal-context (ptree-node-goal context)))
      (let ((target-axiom (get-target-axiom *current-module* target-form t))
	    (subst (resolve-subst-form *current-module* subst-form))
	    (instance nil))
	;;
	(setq instance (make-axiom-instance *current-module* subst target-axiom))
	;; input the instance to current context
	(let ((goal (ptree-node-goal context)))
	  (setf (goal-assumptions goal) (append (goal-assumptions goal) (list instance)))
	  (format t "~%>> initialized the axiom in goal ~s" (goal-name (ptree-node-goal context)))
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (print-axiom-brief instance))
	  (pr-goal (ptree-node-goal context))
	  ;; 
	  (set-operator-rewrite-rule *current-module* instance)
	  (adjoin-axiom-to-module *current-module* instance)
	  (compile-module *current-module*))))))

;;; ==============
;;; CRITICAL PAIRS
;;; ==============

(defun citp-rename-term-variables (suffix list-vars)
  (let ((done nil))
    (dolist (var list-vars)
      (unless (member var done)
	(push var done)
	(setf (variable-name var) (intern (format nil "~a~a" (variable-name var) suffix)))))))

(let ((*renamed-variable-number* 0))
  (declare (type fixnum *renamed-variable-number*))

(defun citp-rename-axiom-variables (axiom)
  (citp-rename-term-variables (incf *renamed-variable-number*) (axiom-variables axiom))
  axiom)
)

(defstruct (cpp (:print-function pr-cpp))
  (t1 nil :type term)			; sigma(lhs[pos])
  (t2 nil :type term)			; sigma(lhs)
  (pos nil :type list)			; occurence of t1 in root term
  (subst nil :type list)		; mgu
  (cpairs nil :type list))		; generated critical pairs in a form of axiom

(defun pr-cpp (cpp &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "~%Critical Pair ---------")
  (let ((*print-indent* (+ *print-indent*))
	(*standard-output* stream))
    (print-next)
    (princ "term 1: ") (term-print-with-sort (cpp-t1 cpp))
    (print-next)
    (princ "term 2: ") (term-print-with-sort (cpp-t2 cpp))
    (print-next)
    (format t "position: ~a" (cpp-pos cpp))
    (print-next)
    (princ "substitution: ") (print-substitution (cpp-subst cpp))
    (when (cpp-cpairs cpp)
      (setq *print-indent* (+ 2 *print-indent*))
      (format t "~%- ~d critical pairs" (length (cpp-cpairs cpp)))
      (dolist (cpair (cpp-cpairs cpp))
	(print-next)
	(print-axiom-brief cpair)))))

(defun compute-overwraps (t1 t2 occur)
  (let ((cpps nil))
    (cond ((term-is-applform? t1)
	   (multiple-value-bind (subst no-match e-eq)
	       (unify t1 t2)
	     (declare (ignore e-eq))
	     (unless no-match
	       (push (make-cpp :t1 (substitution-image-simplifying subst t1)
			       :t2 (substitution-image-simplifying subst t2)
			       :subst subst
			       :pos occur) cpps))
	     (let ((pos 0))
	       (declare (type fixnum pos))
	       (dolist (sub (term-subterms t1))
		 (setq cpps (append cpps (compute-overwraps sub t2 (append occur (cons pos occur)))))
		 (incf pos)))))
	  (t nil))
    cpps))

(defun term-at-pos (pos term)
  (if pos
      (term-at-pos (cdr pos) (term-arg-n term (car pos)))
    term))

(defun replace-term-at (pos term repl-term)
  (let ((target (term-at-pos pos term)))
    (term-replace target repl-term)
    term))

;;;
;;; compute-all-overwrapps : axiom axiom -> List(cpp)
;;;
(defun compute-axiom-overwrapps (ax-1 ax-2)
    (let ((lhs-1 (rule-lhs ax-1))
	  (lhs-2 (rule-lhs ax-2))
	  (cpps nil))
      (setq cpps (compute-overwraps lhs-1 lhs-2 '()))
      cpps))

(defun generate-critical-pairs (cpps ax-1 ax-2)
  (dolist (cpp cpps)
    (let ((subst (cpp-subst cpp))
	  (cpairs nil))
      (let ((cond-1 (substitution-image-simplifying subst (rule-condition ax-1)))
	    (cond-2 (substitution-image-simplifying subst (rule-condition ax-2)))
	    (rhs (substitution-image-simplifying subst (rule-rhs ax-1)))
	    (lhs (replace-term-at (cpp-pos cpp)
				  (substitution-image-simplifying subst (axiom-lhs ax-1))
				  (substitution-image-simplifying subst (axiom-rhs ax-2)))))
	(with-citp-debug ()
	  (format t "~%cond-1: ")(term-print-with-sort cond-1)
	  (format t "~%cond-2: ")(term-print-with-sort cond-2)
	  (format t "~%lhs: ") (term-print-with-sort lhs)
	  (format t "~%rhs: ") (term-print-with-sort rhs))

	(let ((*perform-on-demand-reduction* t))
	  (compile-module *current-module* t)
	  ;; LHS
	  (rewrite lhs *current-module*)
	  ;; RHS
	  (rewrite rhs *current-module*)
	  (unless (term-equational-equal lhs rhs)
	    (let ((ordered-pair (sort (list lhs rhs) #'lrpo)))
	      (pushnew (make-rule :lhs (first ordered-pair)
				  :rhs (second ordered-pair)
				  :condition *bool-true*
				  :type :equation ; might be changed later by command :equqtion or :rule
				  :labels '(cp))
		       cpairs
		       :test #'rule-is-similar?)))

	  ;; Condition
	  (let ((new-cond (make-applform-simple *condition-sort* *bool-cond-op* (list cond-1 cond-2))))
	    (with-citp-debug ()
	      (format t "~%[cp] generated condition: ")
	      (term-print-with-sort new-cond))
	    (rewrite new-cond *current-module*)
	    (with-citp-debug ()
	      (format t "~%     after normalized :")
	      (print-next)
	      (term-print-with-sort new-cond))
	    (unless (is-true? new-cond)
	      (cond ((eq *bool-cond-op* (term-head new-cond))
		     (let ((subs (list-assoc-subterms new-cond *bool-cond-op*)))
		       (setq subs (sort subs #'lrpo))
		       (do* ((sl subs (cdr sl))
			     (lhs (car sl) (car sl))
			     (rhs (cadr sl)))
			   ((null rhs))
			 (pushnew (make-rule :lhs lhs
					     :rhs rhs
					     :condition *bool-true*
					     :type :equation
					     :labels '(cpc))
				  cpairs
				  :test #'rule-is-similar?))))
		    (t  (pushnew (make-rule :lhs new-cond
					    :rhs *bool-true*
					    :condition *bool-true*
					    :type :equation
					    :labels '(cpc))
				 cpairs
				 :test #'rule-is-similar?)))))))
      (setf (cpp-cpairs cpp) cpairs))))

(defun compute-critical-pairs (module axiom1 axiom2)
  (with-in-module (module)
    (let ((ax-1 (citp-rename-axiom-variables (rule-copy-canonicalized axiom1 module)))
	  (ax-2 (citp-rename-axiom-variables (rule-copy-canonicalized axiom2 module)))
	  (cpp-1 nil)
	  (cpp-2 nil))
      (setq cpp-1 (compute-axiom-overwrapps ax-1 ax-2))
      (setq cpp-2 (compute-axiom-overwrapps ax-2 ax-1))
      (generate-critical-pairs cpp-1 ax-1 ax-2)
      (generate-critical-pairs cpp-2 ax-2 ax-1)

      (with-citp-debug ()
	(format t "~%------- cpp-1")
	(print cpp-1)
	(format t "~%------- cpp-2")
	(print cpp-2))
      
      (let ((all-cpairs nil))
	(dolist (cp1 (nconc cpp-1 cpp-2))
	  (setq all-cpairs (nconc all-cpairs (cpp-cpairs cp1))))
	(remove-duplicates all-cpairs :test #'rule-is-similar?)))))

;;; apply-cp : axiom-form axiom-form -> void
;;;
(defun apply-cp (target-1 target-2)
  (let ((context (get-next-proof-context *proof-tree*)))
    (unless context
      (with-output-chaos-error ('no-context)
	(format t "Applying [cp], no context module is established.")))
    (let ((goal (ptree-node-goal context)))
      (with-in-module ((goal-context goal))
	(let ((t1axiom (get-target-axiom *current-module* target-1))
	      (t2axiom (get-target-axiom *current-module* target-2))
	      (cpps nil))
	  (setq cpps
	    (setf (goal-critical-pairs goal) (compute-critical-pairs *current-module* t1axiom t2axiom)))
	  (when cpps
	    (format t "~%>>[cp] :")
	    (let ((*print-indent* (+ 2 *print-indent*)))
	      (dotimes (x (length cpps))
		(print-next)
		(format t "(~d) " (1+ x))
		(let ((ax (nth x cpps)))
		  (term-print-with-sort (axiom-lhs ax))
		  (print-next)
		  (princ "    => ")
		  (term-print-with-sort (axiom-rhs ax)))))))))))

;;; add-critical-pairs
;;;
(defun add-critical-pairs (type direction)
  (let ((context (get-next-proof-context *proof-tree*)))
    (unless context
      (with-output-chaos-error ('no-context)
	(format t "Applying [cp], no context module is established.")))
    (let ((goal (ptree-node-goal context))
	  (applied nil))
      (with-in-module ((goal-context goal))
	(dolist (cps (goal-critical-pairs goal))
	  (setf (rule-type cps) type)
	  (when (eq direction :backward)
	    (let ((rhs (rule-lhs cps))
		  (lhs (rule-rhs cps)))
	      (setf (rule-lhs cps) lhs
		    (rule-rhs cps) rhs)))
	  (compute-rule-method cps)
	  (set-operator-rewrite-rule *current-module* cps)
	  (adjoin-axiom-to-module *current-module* cps)
	  (setq applied (nconc applied (list cps))))
	(when applied
	  (setf (goal-assumptions goal) (nconc (goal-assumptions goal) (nreverse applied)))
	  (format t "~%[cp] added cp ~a~p:" type (length applied))
	  (pr-goal goal))))))

;;; ==============
;;; :lred <term> .
;;; ==============
;;; reduce-in-current-goal : List(token) -> result
;;;
(defun reduce-in-current-goal (token-seq)
  (let ((next-goal-node (get-next-proof-context *proof-tree*)))
    (unless next-goal-node
      (with-output-chaos-error ('no-target)
	(format t ":lred could not find the context.")))
    (perform-reduction* token-seq (goal-context (ptree-node-goal next-goal-node)) :red)))


;;; *****************************************************
;;; APPLY-TACTIC
;;; apply-tactic : ptree-node tactic -> List(ptree-node)
;;; returns the list of generated goal nodes.
;;; -----------------------------------------------------

(defun apply-tactic (ptree-node tactic &optional (verbose t))
  (declare (type ptree-node ptree-node)
	   (type tactic tactic))
  (let ((*chaos-quiet* t)
	(*rwl-search-no-state-report* t))
    (when (goal-is-discharged (ptree-node-goal ptree-node))
      (with-output-chaos-warning ()
	(format t ">> The goal ~s has been proved!." (goal-name (ptree-node-goal ptree-node)))
	(return-from apply-tactic nil)))
    ;; 
    (format t "~%>> Applying ~a to goal ~s" tactic (goal-name (ptree-node-goal ptree-node)))
    (initialize-ptree-node ptree-node)
    (compile-module (goal-context (ptree-node-goal ptree-node)) t)
    (multiple-value-bind (applied next-goals)
	(funcall (tactic-executor tactic) ptree-node)
      (declare (type (or null t) applied)
	       (type list next-goals))
      (unless applied (return-from apply-tactic nil))
      (unless next-goals
	;; reset the current ptree-node status,
	;; i.e., cancel side effents
	(initialize-ptree-node ptree-node)
	(return-from apply-tactic nil))
      (format t "~%>> Generated ~d goal~p" (length next-goals) (length next-goals))
      (add-ptree-children ptree-node next-goals)
      (when verbose
	(dolist (gn (ptree-node-subnodes ptree-node))
	  (pr-goal (ptree-node-goal gn))))
      (ptree-node-subnodes ptree-node))))

;;;
;;; apply-tactics-to-node
;;;
(defun apply-tactics-to-node (target-node tactics)
  (unless tactics (return-from apply-tactics-to-node nil))
  (let ((subs (apply-tactic target-node (car tactics))))
    (if subs
	(dolist (target subs)
	  (apply-tactics-to-node target (cdr tactics)))
      (apply-tactics-to-node target-node (cdr tactics)))))

;;;
;;; apply-tactics 
;;;
(defun apply-tactics (ptree tactics)
  (declare (type ptree ptree)
	   (type list tactics))
  (let ((target (get-next-proof-context ptree)))
    (unless target
      (format t "~%>> All goals have been discharged!")
      (return-from apply-tactics nil))
    (apply-tactics-to-node target tactics))
  (check-success ptree))

;;;
;;; apply-auto
;;;
(defun apply-auto (ptree &optional (tactics .default-tactics.))
  (if (next-proof-target-is-specified?)
      (apply-tactics-to-node (get-next-proof-context ptree) tactics)
    (let ((target-nodes (get-unproved-nodes ptree)))
      (unless target-nodes
	(format t "~%**> All goals have been proved!")
	(return-from apply-auto nil))
      (dolist (tactic tactics)
	(dolist (target-node (get-unproved-nodes ptree))
	  (apply-tactic target-node tactic)))))
  (check-success ptree))

;;;
;;; apply-tactics-to-goal
;;;
(defun apply-tactics-to-goal (ptree name tactics)
  (let ((target-node (find-goal-node ptree name)))
    (unless target-node
      (with-output-chaos-error ('no-named-goal)
	(format t "There is no goal with name ~s." name)))
    (apply-tactics-to-node target-node tactics)
    (check-success ptree)))

;;; EOF
