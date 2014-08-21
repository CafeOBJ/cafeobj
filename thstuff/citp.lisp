;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cexec.lisp,v 1.17 2007-12-29 07:17:02 sawada Exp $
(in-package :chaos)
#|=============================================================================
				    System:CHAOS
				   Module:thstuff
  			           File:citp.lisp
 =============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defun check-context-module ()
  (unless *current-module*
    (with-output-chaos-error ('no-context)
      (format t "No context module is specified, please 'select' or 'open' a module."))))

(defun check-context-module-and-ptree ()
  (check-context-module)
  (unless *proof-tree*
    (with-output-chaos-error ('no-proof-tree)
      (format t "No goal is specified."))))

;;; ============================
;;; CITP related command parsers
;;; ============================

;;;
;;; :goal { <axiom> . <axiom> . .... <axiom> . }
;;;
(defun citp-parse-goal (args)
  (let ((ax-decls nil))
    (dolist (elem (third args))
      (push (parse-module-element-1 elem) ax-decls))
    (nreverse ax-decls)))

;;;
;;; :apply [to <goal-name>] (<tactic> ...)
;;;
;;; (":apply" ("(" ("tc" "rd" "si") ")"))
;;; (":apply" ("to" ("1-1-1")) ("(" ("RD") ")"))
;;;
(defun citp-parse-apply (args)
  (let ((tactic-forms nil)
	(tactics nil)
	(target nil))
    (cond ((string-equal (car (second args)) "to")
	   (setq target (car (second (second args))))
	   (setq tactic-forms (second (third args))))
	  (t (setq tactic-forms (second (second args)))))
    (dolist (tac tactic-forms)
      (let ((tactic (get-tactic tac)))
	(setq tactics (nconc tactics tactic))))
    (cons target tactics)))

;;; citp-parse-ind-on
;;; :ind on (var ... var)
;;; (":ind" "on" "(" ("M:S-1" ... "N:S-N") ")")
;;;
(defun citp-parse-ind-on (args)
  (check-context-module)
  (with-in-module (*current-module*)
    (let ((vars nil))
      (dolist (var-decl (fourth args))
	(let ((var (simple-parse-from-string var-decl)))
	  (when (term-ill-defined var)
	    (with-output-chaos-error ('no-parse)
	      (format t "Illegal variable form: ~s" var-decl)))
	  (unless (term-is-variable? var)
	    (with-output-chaos-error ('no-var)
	      (format t "Invalid argument to ':ind' command: ~s" var-decl)))
	  (push var vars)))
      (nreverse vars))))

;;;
;;; :auto
;;;
(defun citp-parse-auto (args)
  (declare (ignore args))
  (cons :auto (get-default-tactics)))

;;;
;;; :roll back
;;;
(defun citp-parse-roll-back (args)
  (declare (ignore args))
  :roll-back)

;;;
;;; :init {[<label>] | (<axiom>)} by { <var> <- <term>; ...<var> <- <term>; }
;;;
(defun make-axiom-pattern (target)
  (if (equal (first target) "[")
      (cons :label (second target))
    (cons :axiom (second target))))

(defun citp-parse-init (args)
  (let ((target-form (make-axiom-pattern (second args)))
	(subst-list (fifth args))
	(subst-pairs nil))
    (dolist (subst-form subst-list)
      (unless (atom subst-form)
	(push (cons (first subst-form) (third subst-form)) subst-pairs)))
    (with-citp-debug ()
      (format t "~%[:init] target = ~s" target-form)
      (format t "~%        subst  = ~s" subst-pairs))
    (list target-form subst-pairs)))

;;; :cp
;;; (":cp" ("[" ("label-1") "]") "><" ("[" ("label-2") "]")) 
;;; (":cp" ("(" ("ceq" ("LHS") "=" ("RHS") "if" ("C") ".") ")")
;;; "><" ("(" ("ceq" ("LHS-2") "=" ("RHS-2") "if" ("C-2") ".") ")")) 
;;;
(defun citp-parse-critical-pair (args)
  (let ((pat-1 (make-axiom-pattern (second args)))
	(pat-2 (make-axiom-pattern (fourth args))))
    (with-citp-debug ()
      (format t "~%[cp] ~s" pat-1)
      (format t "~%     ~s" pat-2))
    (list pat-1 pat-2)))

;;; :equation/:rule
;;;
(defun citp-parse-equation (args)
  (if (member (car args) '(":equation" "equation") :test #'equal)
      :equation
    :rule))

;;; :backward equation/rule
;;;
(defun citp-parse-backward (args)
  (if (member (second args) '(":equation" "equation") :test #'equal)
      :equation
    :rule))

;;; :select <GoalName>
;;;
(defun citp-parse-select (args)
  (let ((goal-name (car (second args))))
    goal-name))

;;;
;;; citp-parse-lred
;;;
(defun citp-parse-lred (args)
  (second args))

;;; ================================
;;; CITP related command evaluators
;;; ================================

;;; :goal
;;;
(defun eval-citp-goal (goal-ax-decls)
  (check-context-module)
  (with-in-module (*current-module*)
    (let ((axs nil))
      (dolist (a-decl goal-ax-decls)
	(push (parse-axiom-declaration a-decl) axs))
      (begin-proof *current-module* (nreverse axs)))))

;;; :apply/:auto
(defun eval-citp-apply (list-tactic)
  (check-context-module-and-ptree)
  (let ((target (car list-tactic))
	(tactics (cdr list-tactic)))
    (if target
	(case target
	  (:auto (apply-auto *proof-tree*))
	  (otherwise
	   (apply-tactics-to-goal *proof-tree* target tactics)))
      (apply-tactics *proof-tree* tactics))))

;;; :ind on
;;;
(defun eval-citp-ind-on (vars)
  (check-context-module-and-ptree)
  (with-in-module (*current-module*)
    (set-induction-variables vars)))

;;; :roll back
;;;
(defun eval-citp-roll-back (&rest com)
  (declare (ignore com))
  (check-context-module-and-ptree)
  (with-in-module (*current-module*)
    (roll-back *proof-tree*)))
  
;;; :init
;;;
(defun eval-citp-init (args)
  (check-context-module-and-ptree)
  (with-in-module (*current-module*)
    (instanciate-axiom (first args)	; target
		       (second args))))	; variable-term pairs

;;; :cp
(defun eval-citp-critical-pair (args)
  (check-context-module-and-ptree)
  (with-in-module (*current-module*)
    (apply-cp (first args) (second args))))

;;; :equation : {:equation| :rule} -> void
(defun eval-citp-equation (arg)
  (check-context-module-and-ptree)
  (add-critical-pairs arg :forward))

;;; :backward
(defun eval-citp-backward (arg)
  (check-context-module-and-ptree)
  (add-critical-pairs arg :backward))

;;; :select
(defun eval-citp-select (goal-name)
  ;;(check-context-module-and-ptree)
  (unless *proof-tree*
    (with-output-chaos-error ('no-proof)
      (format t "No proof is ongoing.")))
  (select-next-goal goal-name))

;;; :lred
(defun eval-citp-lred (token-sec)
  (check-context-module-and-ptree)
  (reduce-in-current-goal token-sec))

;;; EOF
