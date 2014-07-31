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
;;; :apply (<tactic> ...)
;;; (":apply" ("(" ("tc" "rd" "si") ")"))
(defun citp-parse-apply (args)
  (let ((tactics nil))
    (dolist (tac (second (second args)))
      (let ((tactic (get-tactic tac)))
	(setq tactics (nconc tactics tactic))))
    tactics))

;;;
;;; :ind on var ... var .
;;;
(defun citp-parse-ind-on (args)
  (check-context-module)
  (with-in-module (*current-module*)
    (let ((vars nil))
      (dolist (var-decl (third args))
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
  (get-default-tactics))

;;; ================================
;;; CITP related command evaluators
;;; ================================

;;; :goal
(defun eval-citp-goal (goal-ax-decls)
  (check-context-module)
  (with-in-module (*current-module*)
    (let ((axs nil))
      (dolist (a-decl goal-ax-decls)
	(push (parse-axiom-declaration a-decl) axs))
      (begin-proof *current-module* (nreverse axs)))))

;;; :apply/:auto
(defun eval-citp-apply (list-tactic)
  (unless *proof-tree*
    (with-output-chaos-error ('no-proof-tree)
      (format t "No goal is yet specified.")))
  (apply-tactics *proof-tree* list-tactic))

;;; :ind on
(defun eval-citp-ind-on (vars)
  (check-context-module)
  (unless *proof-tree*
    (with-output-chaos-error ('no-proof-tree)
      (format t "No goal is specified.")))
  (with-in-module (*current-module*)
    (set-indvars (ptree-current *proof-tree*) vars)
    (pr-goal (ptree-node-goal (ptree-current *proof-tree*)))))

;;; EOF



