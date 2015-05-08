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

(defun check-ptree ()
  (unless *proof-tree*
    (with-output-chaos-error ('no-proof-tree)
      (format t "No proof is ongoing."))))

(defun check-context-module-and-ptree ()
  (check-context-module)
  (check-ptree))

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
;;; citp-parse-red
;;;
(defun citp-parse-red (e)
  (let (goal-name
	preterm
	mode)
    (case-equal (first e)
		((":red" ":lred" "lred") (setq mode :red))
		((":exec") (setq mode :exec))
		((":bred") (setq mode :bred)))
    (if (= 4 (length e)) 
	(progn
	  (setq goal-name (cadr (cadr e))); (find-goal-node *proof-tree* (cadr (cadr e)))
	  (setq preterm (nth 2 e)))
      (progn
	(setq goal-name nil)
	(setq preterm (nth 1 e))))
    (list mode goal-name preterm)))

;;;
;;; citp-parse-verbose
;;; :verbose {on | off}
(defun citp-parse-verbose (args)
  (second args))

;;; citp-parse-ctf
;;; :ctf { eq <term> = <term> .}
;;;
(defun citp-parse-ctf (args)
  (let ((ax-form (third args)))
    (with-citp-debug ()
      (format t "~%[:ctf] target = ~s" ax-form))
    ax-form))

;;; citp-parse-csp
;;; :csp { <axiom> ... }
;;;
(defun citp-parse-csp (args)
  (let ((ax-decls nil))
    (dolist (elem (third args))
      (push elem ax-decls))
    (nreverse ax-decls)))

;;; { :show | :describe } <something>
;;;
(defun citp-parse-show (inp)
  (let ((tag (car inp))
	(args (cdr inp))
	(com nil))
    (cond ((member tag '(":show" ":sh") :test #'equal)
	   (setq com :show))
	  ((member tag '(":describe" ":desc") :test #'equal)
	   (setq com :describe))
	  (t (with-output-chaos-error ('internal)
	       (format t "Internal error, unknown citp command ~s" tag))))
    (cons com args)))

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
  (check-ptree)
  (let ((target (car list-tactic))
	(tactics (cdr list-tactic)))
    (let ((*chaos-verbose* nil)
	  (*chaos-quiet* t))
      (if target
	  (case target
	    (:auto (apply-auto *proof-tree*))
	    (otherwise
	     (apply-tactics-to-goal *proof-tree* target tactics)))
	(apply-tactics *proof-tree* tactics)))))

;;; :ind on
;;;
(defun eval-citp-ind-on (vars)
  (check-ptree)
  (with-in-module (*current-module*)
    (set-induction-variables vars)))

;;; :roll back
;;;
(defun eval-citp-roll-back (&rest com)
  (declare (ignore com))
  (check-ptree)
  (with-in-module (*current-module*)
    (roll-back *proof-tree*)))
  
;;; :init
;;;
(defun eval-citp-init (args)
  (check-ptree)
  (with-in-module (*current-module*)
    (instanciate-axiom (first args)	; target
		       (second args))))	; variable-term pairs

;;; :cp
(defun eval-citp-critical-pair (args)
  (check-ptree)
  (with-in-module (*current-module*)
    (apply-cp (first args) (second args))))

;;; :equation : {:equation| :rule} -> void
(defun eval-citp-equation (arg)
  (check-ptree)
  (add-critical-pairs arg :forward))

;;; :backward
(defun eval-citp-backward (arg)
  (check-ptree)
  (add-critical-pairs arg :backward))

;;; :select
(defun eval-citp-select (goal-name)
  (check-ptree)
  (select-next-goal goal-name))

;;; :red, :exec, :bred
(defun eval-citp-red (token-seq)
  (check-ptree)
  (let ((mode (first token-seq))
	(goal-name (second token-seq))
	(pre-term (third token-seq)))
    (reduce-in-goal mode goal-name pre-term)))

;;; :verbose
(defun eval-citp-verbose (token)
  (if (string-equal token "on")
      (setq *citp-verbose* t)
    (if (string-equal token "off")
	(setq *citp-verbose* nil)
      (with-output-chaos-error ('invlid-value)
	(format t "Unknown parameter ~s." token)))))

;;; :ctf
;;;
(defun eval-citp-ctf (ax-form)
  (check-ptree)
  (with-in-module (*current-module*)
    (reset-rewrite-counters)
    (begin-rewrite)
    (apply-ctf ax-form)
    (end-rewrite)
    (report-citp-stat)
    (check-success *proof-tree*)))

;;; :csp
(defun eval-citp-csp (goal-ax-decls)
  (check-ptree)
  (with-in-module (*current-module*)
    (reset-rewrite-counters)
    (begin-rewrite)
    (apply-csp (nreverse goal-ax-decls))
    (end-rewrite)
    (report-citp-stat)
    (check-success *proof-tree*)))

;;; :show, :describe
(defun eval-citp-show (token)
  (let* ((com (car token))
	 (describe (eq com :describe))
	 (target (cadr token))
	 (rest-args (cddr token)))
    (cond ((member target '("unproved" "unp") :test #'equal)
	   (check-ptree)
	   (print-unproved-goals *proof-tree*))
	  ((equal target "goal")
	   (check-ptree)
	   (let ((name (car rest-args)))
	     (print-named-goal *proof-tree* name)))
	  ((equal target "proof")
	   (let ((name (car rest-args)))
	     (when (or (null name) (equal name "."))
	       (setq name "root"))
	     (print-proof-tree name describe)))
	  ((member target '("." "current") :test #'equal)
	   (check-ptree)
	   (print-current-goal describe))
	  (t (with-output-chaos-error ('unknown)
	       (format t "Unknown parameter to :show/:describe ~S" target))))))

;;; EOF
